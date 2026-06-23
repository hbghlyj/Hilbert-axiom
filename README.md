# Neutral geometry from Hilbert's axioms (Lean 4 port)

This directory contains a Lean 4 port of the foundational layers of T. Zhao's
*Hilbert's axioms in Lean* development (originally written in Lean 3), adapted to
the project's Lean 4 / Mathlib toolchain. It develops **neutral geometry**
(geometry without the parallel postulate, valid in both the Euclidean and
hyperbolic planes) purely synthetically from Hilbert's axioms.

All declarations below are fully proved (no `sorry`, only the standard axioms
`propext`, `Classical.choice`, `Quot.sound`).

## Files (in dependency order)

* `Incidence.lean` — **Group I (Incidence)**. The class `IncidenceGeometry`
  (axioms I1–I3), lines, collinearity (`col`/`noncol`) and their basic theory.

* `Segment.lean` — **Group II (Order/Betweenness)**. The class
  `IncidenceOrderGeometry` extending incidence with a betweenness relation
  `between` (axioms B1–B4, with **B4 = Pasch's axiom**), segments (`-ₛ`), and the
  derived **Pasch theorem** `pasch`.

* `Sidedness.lean` — same/different side of a line and of a point
  (`same_side_line`, `diff_side_line`, `same_side_pt`, `diff_side_pt`),
  plane separation, line separation, and the betweenness-transitivity theorems
  (`between_trans`, `between_trans'`, …).

* `Angle.lean` — rays (`-ᵣ`), angles (written `∠[a, o, b]`, vertex `o`),
  interior of an angle (`inside_ang`), supplementary angles, and the
  **crossbar theorem** `crossbar`.

* `Congruence.lean` — **Group III (Congruence)**. The class `HilbertPlane`
  extending `IncidenceOrderGeometry` with segment congruence (`≅ₛ`) and angle
  congruence (`≅ₐ`) subject to Hilbert's axioms **C1–C6** (C6 = SAS). Develops
  triangle congruence (`≅ₜ`), `SAS`, segment/angle transport, supplementary-angle
  congruence, angle addition/subtraction, and vertical angles (I.15).

* `SegLt.lean` — segment ordering `<ₛ` with congruence invariance, transitivity
  and trichotomy (`seg_tri`).

* `AngLt.lean` — angle ordering `<ₐ` with congruence invariance, transitivity
  and trichotomy (`ang_tri`).

* `Elements.lean` — selected propositions of Euclid's Book I built on the above:
  isosceles base angles (**I.5/I.6**), **SSS** (I.8), existence of isosceles
  triangles, angle bisectors (**I.9**), midpoints (**I.10**), the exterior-angle
  inequality (**I.16**), and the **angle–side inequality** (**I.18**,
  `greater_side_ang`): in a triangle the greater side lies opposite the greater
  angle. The corollary `ang_opposite_greater_side` states I.18 in the exact
  labelling of the request (`AB > AC ⟹ ∠ACB > ∠ABC`).

* `Diameter.lean` — the synthetic **diameter inequality**: for two points `p, q`
  of the closed triangle `△abc`, `|pq| ≤ max {|ab|, |bc|, |ac|}`
  (`dist_le_max_side`). Includes the converse scalene inequality **I.19**
  (`greater_ang_side`), the "point of a segment is no farther than its farther
  endpoint" lemma (`seg_lt_max_of_between`), the closed-triangle membership
  predicate (`in_closed_triang`) and the cevian-reachability theorem
  (`reach_of_closed`, from the crossbar theorem).

## Relation to the requested theorem

The original request is to prove, in neutral geometry, that for two points `p, q`
in a closed triangle `△abc`, `|pq| ≤ max {|ab|, |bc|, |ac|}`.

* The **Group III (Congruence)** layer is now formalized (`Congruence.lean`,
  `SegLt.lean`, `AngLt.lean`, `Elements.lean`). In particular the **scalene /
  angle–side inequality** ("the greater side lies opposite the greater angle")
  is proved synthetically from Hilbert's axioms as `Elements.greater_side_ang`
  (Euclid I.18), via the isosceles-triangle theorem (I.5) and the exterior-angle
  theorem (I.16), exactly as in the requested SAS/cut-off argument. This holds in
  every Hilbert plane, hence in both the Euclidean and hyperbolic planes.

* The **fully synthetic proof of the diameter bound**
  `|pq| ≤ max {|ab|, |bc|, |ac|}` is now complete, in `Diameter.lean`
  (`dist_le_max_side`, with the restatement `not_all_sides_lt`). It is proved
  purely from Hilbert's axioms, hence holds in **both** the Euclidean and the
  hyperbolic plane. Since a Hilbert plane has no real-valued distance, "`pq` does
  not exceed the longest side" is phrased with the synthetic segment ordering: we
  write `m ≤ₛ n` for `¬ (n <ₛ m)` (for proper segments this is `m <ₛ n ∨ m ≅ₛ n`,
  by `seg_tri`), and prove
  `(p-ₛq) ≤ₛ (a-ₛb) ∨ (p-ₛq) ≤ₛ (b-ₛc) ∨ (p-ₛq) ≤ₛ (a-ₛc)`,
  which is exactly `pq ≤ max {ab, bc, ac}` (the maximum is whichever side is
  largest).

  The closed triangle (interior, sides and vertices) is `in_closed_triang`. The
  proof follows the convexity idea: from any vantage point a point of a segment
  is no farther than the farther endpoint (`seg_lt_max_of_between`, an instance
  of the exterior-angle inequality I.16 and the scalene inequalities I.18/I.19 —
  the converse I.19 is proved here as `greater_ang_side`); every closed-triangle
  point lies on a cevian from a vertex to the opposite side (`reach_of_closed`,
  via the crossbar theorem); hence the distance from any fixed point to a
  triangle point is bounded by the distances to the vertices (`cevian`), and the
  distance from a vertex to a triangle point is bounded by the two adjacent sides
  (`vertex_to_pt`). All of `Diameter.lean` builds with no `sorry` and only the
  standard axioms `propext`, `Classical.choice`, `Quot.sound`.
