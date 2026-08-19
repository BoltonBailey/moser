# Claude transcripts

A record of the AI-assisted work done in this repository.

Claude Code writes one JSONL file per session under
`~/.claude/projects/<slugified-repo-path>/`. Those files live outside the
repository and are pruned over time, so they are exported here:

* `raw/<date>_<session>.jsonl` — the session file, copied verbatim. This is the
  authoritative record: every message, tool call and tool result.
* `<date>_<session>.md` — a readable rendering of the same session: the prompts,
  Claude's replies, and each tool call with its output abridged. Good for
  reading and for `grep`; not a substitute for the raw file.

## Exporting

From the repository root:

```sh
python3 transcripts/export_transcripts.py           # sessions that have ended
python3 transcripts/export_transcripts.py --all     # include the running one
python3 transcripts/export_transcripts.py --session <id>
```

The session you are currently in is skipped by default — its JSONL is still
being appended to, so exporting it would capture only part of the conversation.
Re-run the script once the session ends to add it. Re-running is idempotent:
existing exports are simply overwritten with the fuller version.

## Sessions so far

| date | session | topic |
| --- | --- | --- |
| 2026-06-25 | `e8faeea7` | Define `moserCoverNumber` in terms of `minimalCoverArea` |
| 2026-08-14 | `bb83442c` | Working-set spine: leaf lemmas, containment and area bridges |

The session that produced `Moser/Real/{Approximation, PolygonalApprox, Pruning,
ClippedArea, ExplicitBounds, Certificate, CertificateTen, CertificateWidget}.lean`
(2026-08-18/19) was still running when this folder was created; run the exporter
again to record it.
