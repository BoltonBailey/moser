/-
Prototype of the expansion-based branch-and-bound search (not part of the library build).

Node invariant: any pinned small cover `K` (convex, covers all worms, contains the
pinned `InitialWorm`, area ≤ `areaThreshold`) contains some working polygon `p`.

Node expansion:
1. Build mitered outer offsets `Qε ⊇ p^ε` and `Qh ⊇ p^{ε/2}` (edge half-spaces
   pushed outward, intersected).
2. Certificate: if `diam(Qε)² < 1`, the unit segment worm fits in no subset of `Qε`,
   so `K ⊄ Qε`; convexity gives a point `w ∈ K` on `∂Qε`.
3. Choose sample points `z i` near `∂Qh`. Each `z` "captures" the set
   `cone(z) = {z + t(z−x) : x ∈ p, t ≥ 0}`: if `w ∈ cone(z)` then `z ∈ hull(p ∪ {w}) ⊆ K`.
4. Cover `∂Qε` by the cones (checked exactly: subdivide edges; a sub-segment is
   covered by `z` iff both endpoints are in `cone(z)`, cones being convex).
   Pieces covered by a *refuted* `z` (i.e. `area (hull(p ∪ {z})) > areaThreshold`)
   are dead; the rest spawn children `hull(p ∪ {z})`.
5. A node with all pieces dead is CLOSED (refuted).

Run with:  BUDGET=300 lake env lean Scratch.lean
-/
import Moser.Manipulation.Operations
import Moser.Geometry.AllowableAdditions

open Moser

def ratToFloat (q : ℚ) : Float := Float.ofInt q.num / Float.ofNat q.den

abbrev CPoly := ConvexPolygon ℚ

instance : Inhabited CPoly := ⟨InitialWorm⟩

namespace Proto

/-- Mitered outer offset: push every edge half-space outward by at least `eps`
(at most `eps·(1 + 1/100)`), then intersect. Contains the true `eps`-thickening. -/
def offsetPoly (p : CPoly) (eps : ℚ) (heps : 0 < eps) : Option CPoly :=
  match p.toHalfSpaces with
  | none => none
  | some hs =>
    ConvexPolygon.ofHalfSpaces
      (hs.map (fun h => h.moveOutward eps (eps / 100) heps (by positivity)))

/-- Squared diameter of a convex polygon (max over vertex pairs). -/
def diamSq (p : CPoly) : ℚ :=
  (p.vertex_list.flatMap fun a => p.vertex_list.map fun b => Point.distSq a b).foldl max 0

/-- Extreme directions of the capture cone `{z + t(z−x) : x ∈ p, t ≥ 0}`:
`da` has all generators weakly counterclockwise of it, `db` weakly clockwise. -/
def coneExtremes (p : CPoly) (z : Point ℚ) : Option (Point ℚ × Point ℚ) :=
  let ds := p.vertex_list.map (fun v => z - v)
  match ds.find? (fun d => ds.all (fun e => decide (0 ≤ Point.crossProduct d e))),
        ds.find? (fun d => ds.all (fun e => decide (Point.crossProduct d e ≤ 0))) with
  | some da, some db => some (da, db)
  | _, _ => none

/-- `w ∈ cone(z)` test given the extreme directions. -/
def inConeAux (da db z w : Point ℚ) : Bool :=
  let d := w - z
  decide (0 ≤ Point.crossProduct da d) && decide (Point.crossProduct db d ≤ 0)

/-- Round to the grid `(1/N)·ℤ²` to keep child polygons' rationals small. -/
def roundPt (v : Point ℚ) (N : ℕ) : Point ℚ :=
  ![(round (v 0 * N) : ℤ) / N, (round (v 1 * N) : ℤ) / N]

/-- Sample points: vertices of `qh` plus `m` interior points per edge, grid-rounded. -/
def samplesOf (qh : CPoly) (m : ℕ) (N : ℕ) : List (Point ℚ) :=
  let vs := qh.vertex_list
  let edges := vs.zip (vs.rotate 1)
  ((vs ++ edges.flatMap (fun ab =>
    (List.range m).map (fun i =>
      ab.1 + (((i : ℚ) + 1) / ((m : ℚ) + 1)) • (ab.2 - ab.1)))).map (roundPt · N)).dedup

inductive Expansion where
  | closed
  | children (cs : List CPoly)
  | stuckCert (dsq : ℚ)
  | stuckCover

def epsCandidates : List ℚ := [3/20, 1/10, 3/40, 1/20, 1/40, 1/100]

def expand (p : CPoly) : Expansion := Id.run do
  let mut sawCoverFail := false
  for eps in epsCandidates do
    if heps : 0 < eps then
      match offsetPoly p eps heps, offsetPoly p (eps / 2) (by positivity) with
      | some qe, some qh =>
        if diamSq qe < 1 then
          for mk in [(1, 6), (3, 12)] do
            let zs := (samplesOf qh mk.1 1024).filter (fun z => !p.contains z)
            let zinfo := zs.filterMap fun z =>
              match coneExtremes p z, ConvexPolygon.ofList (z :: p.vertex_list) with
              | some (da, db), some child =>
                some (z, da, db, child, decide (areaThreshold < child.area))
              | _, _ => none
            let vs := qe.vertex_list
            let pieces := (vs.zip (vs.rotate 1)).flatMap fun ab =>
              (List.range mk.2).map fun i =>
                (ab.1 + ((i : ℚ) / (mk.2 : ℚ)) • (ab.2 - ab.1),
                 ab.1 + (((i : ℚ) + 1) / (mk.2 : ℚ)) • (ab.2 - ab.1))
            let mut ok := true
            let mut lives : Array CPoly := #[]
            let mut liveZ : Array (Point ℚ) := #[]
            for xy in pieces do
              let covers := zinfo.filter fun info =>
                inConeAux info.2.1 info.2.2.1 info.1 xy.1
                  && inConeAux info.2.1 info.2.2.1 info.1 xy.2
              if covers.any (fun info => info.2.2.2.2) then
                pure ()  -- dead piece: captured by a refuted point
              else
                match covers.head? with
                | some info =>
                  if !liveZ.contains info.1 then
                    liveZ := liveZ.push info.1
                    lives := lives.push info.2.2.2.1
                | none => ok := false
            if ok then
              if lives.isEmpty then return .closed
              else return .children lives.toList
            else
              sawCoverFail := true
      | _, _ => pure ()
  if sawCoverFail then return .stuckCover else return .stuckCert (diamSq p)

def run (budget : ℕ) : IO Unit := do
  let mut queue : Array (ℕ × CPoly) := #[(0, InitialWorm)]
  let mut processed := 0
  let mut closed := 0
  let mut stuckCertN := 0
  let mut stuckCoverN := 0
  let mut spawned := 0
  let mut maxArea : ℚ := 0
  let mut maxDepth := 0
  let mut stuckSamples : Array (ℕ × ℚ × ℚ × ℕ) := #[]
  let t0 ← IO.monoMsNow
  for _ in List.range budget do
    if queue.isEmpty then break
    -- best-first: pop max area
    let mut bi := 0
    for i in List.range queue.size do
      if (queue[i]!).2.area > (queue[bi]!).2.area then bi := i
    let (d, p) := queue[bi]!
    queue := queue.eraseIdx! bi
    processed := processed + 1
    maxDepth := max maxDepth d
    maxArea := max maxArea p.area
    let tn0 ← IO.monoMsNow
    let result ← IO.lazyPure (fun _ => expand p)
    let tn1 ← IO.monoMsNow
    IO.println s!"node {processed}: depth {d} verts {p.vertex_count} area {ratToFloat p.area} expand {tn1 - tn0} ms"
    (← IO.getStdout).flush
    match result with
    | .closed => closed := closed + 1
    | .children cs =>
      spawned := spawned + cs.length
      for c in cs do queue := queue.push (d + 1, c)
    | .stuckCert dsq =>
      stuckCertN := stuckCertN + 1
      if stuckSamples.size < 8 then
        stuckSamples := stuckSamples.push (d, p.area, dsq, p.vertex_count)
    | .stuckCover =>
      stuckCoverN := stuckCoverN + 1
  let t1 ← IO.monoMsNow
  IO.println s!"--- summary after {processed} nodes ({t1 - t0} ms) ---"
  IO.println s!"closed(refuted)={closed} stuckCert={stuckCertN} stuckCover={stuckCoverN} spawned={spawned}"
  IO.println s!"max area reached {ratToFloat maxArea} (threshold {ratToFloat areaThreshold}), max depth {maxDepth}"
  IO.println s!"queue remaining: {queue.size}"
  if !queue.isEmpty then
    let areas := queue.toList.map (fun dp => dp.2.area)
    IO.println s!"  queue area range [{ratToFloat (areas.foldl min 1)}, {ratToFloat (areas.foldl max 0)}]"
  for s in stuckSamples do
    IO.println s!"  stuck(cert): depth {s.1} area {ratToFloat s.2.1} diam {Float.sqrt (ratToFloat s.2.2.1)} verts {s.2.2.2}"

end Proto

#eval do
  let budget := ((← IO.getEnv "BUDGET").getD "200").toNat!
  Proto.run budget
