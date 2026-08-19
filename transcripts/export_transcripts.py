#!/usr/bin/env python3
"""Export Claude Code session transcripts for this repository.

Claude Code stores one JSONL file per session under
`~/.claude/projects/<slugified-repo-path>/`. This script copies those files
verbatim into `transcripts/raw/` and renders a readable Markdown version
alongside, so the repository keeps a durable record of the AI work done in it.

Usage (from the repository root):

    python3 transcripts/export_transcripts.py            # completed sessions
    python3 transcripts/export_transcripts.py --all      # include the running one
    python3 transcripts/export_transcripts.py --session ID

The session currently running is skipped by default: its JSONL is still being
appended to, so exporting it would record only part of the conversation. Re-run
the script after the session ends to capture it.
"""

from __future__ import annotations

import argparse
import json
import os
import shutil
import time
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
OUT = REPO / "transcripts"
RAW = OUT / "raw"

# how much of a tool call / result to keep in the Markdown rendering
TOOL_INPUT_CHARS = 800
TOOL_RESULT_CHARS = 400
# a session file touched this recently is assumed to be the one running now
RUNNING_SECONDS = 15 * 60


def session_dir() -> Path:
    """The `~/.claude/projects` directory holding this repository's sessions."""
    slug = str(REPO).replace("/", "-").replace("_", "-").replace(".", "-")
    return Path.home() / ".claude" / "projects" / slug


def clip(text: str, limit: int) -> str:
    text = text.rstrip()
    if len(text) <= limit:
        return text
    return text[:limit].rstrip() + f"\n… [{len(text) - limit} more characters]"


def block_to_md(block: dict) -> str:
    kind = block.get("type")
    if kind == "text":
        return block.get("text", "").strip()
    if kind == "thinking":
        return ""  # reasoning blocks are not stored in readable form
    if kind == "tool_use":
        name = block.get("name", "?")
        raw = json.dumps(block.get("input", {}), indent=2, ensure_ascii=False)
        return f"<details><summary>🛠 <code>{name}</code></summary>\n\n```json\n{clip(raw, TOOL_INPUT_CHARS)}\n```\n\n</details>"
    if kind == "tool_result":
        content = block.get("content")
        if isinstance(content, list):
            content = "\n".join(
                c.get("text", "") for c in content if isinstance(c, dict)
            )
        text = clip(str(content or ""), TOOL_RESULT_CHARS)
        flag = " (error)" if block.get("is_error") else ""
        return f"<details><summary>↳ result{flag}</summary>\n\n```\n{text}\n```\n\n</details>"
    if kind == "image":
        return "_[image]_"
    return f"_[{kind}]_"


def render(path: Path, raw_name: str) -> tuple[str, str, str]:
    """Return (markdown, title, first-timestamp) for one session file."""
    entries = []
    title = ""
    first = last = ""
    for line in path.open():
        line = line.strip()
        if not line:
            continue
        try:
            entries.append(json.loads(line))
        except json.JSONDecodeError:
            continue  # a partially written final line (session still running)

    for d in entries:
        if d.get("type") == "ai-title" and d.get("aiTitle"):
            title = d["aiTitle"]
        ts = d.get("timestamp")
        if ts:
            first = first or ts
            last = ts

    body: list[str] = []
    n_user = n_asst = 0
    for d in entries:
        kind = d.get("type")
        if kind not in ("user", "assistant"):
            continue
        if d.get("isSidechain"):
            continue  # sub-agent chatter
        message = d.get("message") or {}
        content = message.get("content")
        if isinstance(content, str):
            parts = [content.strip()]
        else:
            parts = [block_to_md(b) for b in (content or [])]
        parts = [p for p in parts if p]
        if not parts:
            continue
        if kind == "user":
            n_user += 1
            body.append("### 👤 User\n\n" + "\n\n".join(parts))
        else:
            n_asst += 1
            body.append("### 🤖 Claude\n\n" + "\n\n".join(parts))

    header = [
        f"# {title or path.stem}",
        "",
        f"- **Session** `{path.stem}`",
        f"- **Started** {first or '?'}",
        f"- **Ended** {last or '?'}",
        f"- **Turns** {n_user} user / {n_asst} assistant",
        "",
        "Rendered from the session JSONL by `transcripts/export_transcripts.py`;",
        "tool calls and their outputs are abridged. The verbatim record is in",
        f"`transcripts/raw/{raw_name}`.",
        "",
        "---",
        "",
        "",
    ]
    return "\n".join(header) + "\n\n---\n\n".join(body) + "\n", title, first


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--all", action="store_true",
                    help="also export the session that is currently running")
    ap.add_argument("--session", help="export only this session id")
    args = ap.parse_args()

    src = session_dir()
    if not src.is_dir():
        raise SystemExit(f"no session directory at {src}")

    current = os.environ.get("CLAUDE_SESSION_ID", "")
    RAW.mkdir(parents=True, exist_ok=True)
    now = time.time()

    for path in sorted(src.glob("*.jsonl")):
        sid = path.stem
        if args.session and sid != args.session:
            continue
        # a file still being appended to belongs to a session that is running
        running = sid == current or (now - path.stat().st_mtime) < RUNNING_SECONDS
        if running and not (args.all or args.session):
            print(f"skipping {sid}: session still running "
                  f"(re-run after it ends, or pass --all)")
            continue
        first_ts = ""
        for line in path.open():
            try:
                first_ts = json.loads(line).get("timestamp", "")
            except json.JSONDecodeError:
                continue
            if first_ts:
                break
        if not first_ts:
            continue
        base = f"{first_ts[:10]}_{sid[:8]}"
        markdown, title, _ = render(path, f"{base}.jsonl")
        shutil.copy2(path, RAW / f"{base}.jsonl")
        (RAW / f"{base}.jsonl").chmod(0o644)
        (OUT / f"{base}.md").write_text(markdown)
        print(f"exported {base}  {title}" + ("  [PARTIAL: still running]" if running else ""))


if __name__ == "__main__":
    main()
