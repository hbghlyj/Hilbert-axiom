import RequestProject.Hilbert.Elements

/-!
# The diameter inequality, fully synthetically (Hilbert's axioms)

We prove, purely from Hilbert's axioms (so valid in **both** the Euclidean and the
hyperbolic plane), the inequality of the original request:

> Given a triangle `△ a b c` and two points `p, q` of the closed triangle (interior,
> sides, or vertices), the segment `p q` is no longer than the longest side, i.e.
> `|pq| ≤ max {|ab|, |bc|, |ac|}`.

Since a Hilbert plane has no real-valued distance, "no longer than" is expressed by the
synthetic segment ordering `<ₛ`/`≅ₛ`.  We write `m ≤ₛ n` for "`m` does not exceed `n`",
defined as `¬ (n <ₛ m)`; for proper segments this agrees with `m <ₛ n ∨ m ≅ₛ n` (by
trichotomy `seg_tri`).  The statement

`(p-ₛq) ≤ₛ (a-ₛb) ∨ (p-ₛq) ≤ₛ (b-ₛc) ∨ (p-ₛq) ≤ₛ (a-ₛc)`

is exactly "`pq ≤ max {ab, bc, ac}`": the maximum is whichever side is the largest, and
`pq ≤ max` is equivalent (under trichotomy, the three sides being proper) to `pq` being
`≤ₛ` one of them.

The proof follows the convexity idea: a point of a segment is, from any vantage point,
no farther than the farther endpoint (`seg_le_max_of_between`, an instance of the
exterior-angle / scalene inequalities); every point of the closed triangle lies on a
cevian from a vertex to the opposite side (`reach_of_closed`, via the crossbar theorem);
hence the distance from any fixed point to a triangle point is bounded by the distances
to the vertices, and the distance from a vertex to a triangle point is bounded by the two
adjacent sides.
-/

set_option maxHeartbeats 1000000

universe u

namespace Hilbert

open IncidenceGeometry IncidenceOrderGeometry HilbertPlane

variable [C : HilbertPlane]

/-- `m ≤ₛ n` ("`m` does not exceed `n`") means `n` is not strictly shorter than `m`.
For proper segments this is `m <ₛ n ∨ m ≅ₛ n`. -/
def seg_le (m n : seg) : Prop := ¬ (n <ₛ m)

@[inherit_doc] notation:50 m " ≤ₛ " n => seg_le m n

/-! ## Order helpers -/

/-- Nothing is `<ₛ`-below a degenerate segment (a degenerate segment is never the larger
of a strict inequality). -/
lemma not_lt_degenerate {a : Pts} {n : seg} : ¬ (n <ₛ (a-ₛa)) := by
  rintro ⟨x, y, z, h₁, h₂, h₃⟩
  have : y = a ∧ z = a := by
    have := two_pt_seg_pt h₁.symm
    tauto
  obtain ⟨rfl, rfl⟩ := this
  exact (between_neq h₂).2.1 rfl

/-- `<ₛ` is irreflexive. -/
lemma seg_lt_irrefl {m : seg} : ¬ (m <ₛ m) := by
  intro h
  exact (seg_tri (seg_lt_proper h) (seg_lt_proper h)).2.2.1 ⟨h, h⟩

/-- `≤ₛ` is reflexive. -/
lemma seg_le_refl (m : seg) : m ≤ₛ m := seg_lt_irrefl

/-- `<ₛ` implies `≤ₛ`. -/
lemma seg_lt_le {m n : seg} (h : m <ₛ n) : m ≤ₛ n := by
  intro h2
  exact (seg_tri (seg_lt_proper h2) (seg_lt_proper h)).2.2.1 ⟨h, h2⟩

/-- Transitivity of `≤ₛ` through a proper middle segment. -/
lemma seg_le_trans {m n l : seg} (hn : seg_proper n) (h1 : m ≤ₛ n) (h2 : n ≤ₛ l) :
    m ≤ₛ l := by
  intro hlm
  have hm := seg_lt_proper hlm
  rcases (seg_tri hm hn).1 with h | h | h
  · exact h2 (seg_lt_trans hlm h)
  · exact h2 ((seg_lt_congr h).2 hn hlm)
  · exact h1 h

/-- A proper sub-segment is strictly shorter: `between u x v → (u-ₛx) <ₛ (u-ₛv)`. -/
lemma sub_seg_lt {u x v : Pts} (h : between u x v) : (u-ₛx) <ₛ (u-ₛv) :=
  two_pt_seg_lt.2 ⟨x, h, seg_congr_refl _⟩

/-! ## The converse scalene inequality (Euclid I.19) -/

/-
Euclid I.19: the side opposite the greater angle is the greater side.
If in triangle `abc` the angle at `c` is less than the angle at `b`, then side `ab`
(opposite `c`) is less than side `ac` (opposite `b`).
-/
lemma greater_ang_side {a b c : Pts} (habc : noncol a b c)
    (h : ∠[a, c, b] <ₐ ∠[a, b, c]) : (a-ₛb) <ₛ (a-ₛc) := by
  have h₁ : seg_proper (a-ₛb) ∧ seg_proper (a-ₛc) := by
    grind +suggestions;
  have h₂ : ang_proper (∠[a, c, b]) ∧ ang_proper (∠[a, b, c]) := by
    grind +suggestions;
  have := Hilbert.ang_tri h₂.1 h₂.2; simp_all +decide ;
  grind +suggestions

/-! ## The key "max of endpoints" lemma -/

/-
Noncollinear case of `seg_le_max_of_between`: if `o` is off the line `uv` and `p`
is strictly between `u` and `v`, then `op` is strictly shorter than `ou` or than `ov`.
-/
lemma seg_lt_max_of_between_noncol {o u v p : Pts}
    (houv : noncol o u v) (hupv : between u p v) :
    ((o-ₛp) <ₛ (o-ₛu)) ∨ ((o-ₛp) <ₛ (o-ₛv)) := by
  -- By the properties of angles and segments, we know that if $p$ is between $u$ and $v$, then $\angle[opu]$ and $\angle[opv]$ are both proper.
  have h_ang_proper : ang_proper (∠[o, p, u]) ∧ ang_proper (∠[o, p, v]) := by
    have h_noncol_opu : noncol o p u := by
      simp_all +decide [ noncol ];
      grind +suggestions
    have h_noncol_opv : noncol o p v := by
      by_contra h_contra;
      unfold noncol at *;
      grind +suggestions
    exact ⟨by
    grind +suggestions, by
      grind +suggestions⟩;
  -- By the properties of angles and segments, we know that if $p$ is between $u$ and $v$, then $\angle[opu]$ and $\angle[opv]$ are both proper. Therefore, we can apply the angle trichotomy (ang_tri) to them.
  obtain ⟨h_cases⟩ : (∠[o, p, u] <ₐ ∠[o, p, v]) ∨ (∠[o, p, u] ≅ₐ ∠[o, p, v]) ∨ (∠[o, p, v] <ₐ ∠[o, p, u]) := by
    have := @ang_tri C;
    exact this h_ang_proper.1 h_ang_proper.2 |>.1;
  · have h_contradiction : ∠[o, v, p] <ₐ ∠[o, p, v] := by
      have := @ang_exter_lt_inter C;
      grind +suggestions;
    grind +suggestions;
  · have := ang_exter_lt_inter ( show noncol o u p from ?_ ) ( show between u p v from hupv );
    · grind +suggestions;
    · grind +suggestions

/-
Pure-order fact: with `o` on the line `uv`, `p` between `u` and `v`, and `o` distinct
from `u, v, p`, the point `p` is between `o` and one of the endpoints.
-/
lemma between_outer {o u v p : Pts}
    (hcol : col o u v) (hupv : between u p v) (hop : o ≠ p) (hou : o ≠ u) (hov : o ≠ v) :
    between o p u ∨ between o p v := by
  cases eq_or_ne p u <;> cases eq_or_ne p v <;> simp_all +decide;
  · grind +suggestions;
  · grind +suggestions;
  · grind +suggestions;
  · have h_cases : between o u v ∨ between o v u ∨ between u o v := by
      grind +suggestions
    generalize_proofs at *; (
    rcases h_cases with ( h_cases | h_cases | h_cases );
    · grind +suggestions;
    · grind +suggestions;
    · have h_cases2 : between u p o ∨ between u o p := by
        apply same_side_pt_between; exact (by
        grind +suggestions); exact (by
        tauto);
      generalize_proofs at *; (
      grind +suggestions))

/-- Collinear case: if `o` is on the line `uv` and `p` is strictly between `u` and `v`
(with `o ≠ p`), then `op` is strictly shorter than `ou` or than `ov`. -/
lemma seg_lt_max_of_between_col {o u v p : Pts}
    (hcol : col o u v) (hupv : between u p v) (hop : o ≠ p) :
    ((o-ₛp) <ₛ (o-ₛu)) ∨ ((o-ₛp) <ₛ (o-ₛv)) := by
  by_cases hou : o = u
  · subst hou
    exact Or.inr (sub_seg_lt hupv)
  · by_cases hov : o = v
    · subst hov
      exact Or.inl (sub_seg_lt ((between_symm u p o).1 hupv))
    · rcases between_outer hcol hupv hop hou hov with h | h
      · exact Or.inl (sub_seg_lt h)
      · exact Or.inr (sub_seg_lt h)

/-- If `p` is strictly between `u` and `v` and `o ≠ p`, then `op` is strictly shorter
than `ou` or than `ov`. -/
lemma seg_lt_max_of_between {o u v p : Pts}
    (hupv : between u p v) (hop : o ≠ p) :
    ((o-ₛp) <ₛ (o-ₛu)) ∨ ((o-ₛp) <ₛ (o-ₛv)) := by
  by_cases h : col o u v
  · exact seg_lt_max_of_between_col h hupv hop
  · exact seg_lt_max_of_between_noncol h hupv

/-! ## Closed segment / closed triangle membership -/

/-- `x` lies on the closed segment from `u` to `v` (an endpoint or strictly between). -/
def in_closed_seg (x u v : Pts) : Prop := x = u ∨ x = v ∨ between u x v

/-- `p` is in the open interior of triangle `abc` (inside all three angles). -/
def in_triang_interior (p a b c : Pts) : Prop :=
  inside_ang p (∠[b, a, c]) ∧ inside_ang p (∠[a, b, c]) ∧ inside_ang p (∠[a, c, b])

/-- `p` is in the closed triangle `abc` (on a side or in the interior; the vertices are
endpoints of the sides). -/
def in_closed_triang (p a b c : Pts) : Prop :=
  in_closed_seg p a b ∨ in_closed_seg p b c ∨ in_closed_seg p a c
    ∨ in_triang_interior p a b c

/-
From any vantage point `o`, a point of the closed segment `bc` is no farther than the
farther of `b`, `c`.
-/
lemma seg_le_max_of_closed_seg {o b c d : Pts} (hd : in_closed_seg d b c) :
    ((o-ₛd) ≤ₛ (o-ₛb)) ∨ ((o-ₛd) ≤ₛ (o-ₛc)) := by
  rcases hd with ( rfl | rfl | h );
  · exact Or.inl ( seg_le_refl _ );
  · exact Or.inr ( seg_le_refl _ );
  · by_cases ho : o = d;
    · subst ho;
      exact Or.inl ( not_lt_degenerate );
    · obtain h | h := seg_lt_max_of_between h ho;
      · exact Or.inl <| seg_lt_le h;
      · exact Or.inr ( seg_lt_le h )

/-! ## Reachability: every closed-triangle point lies on a cevian from `a` -/

/-
An interior point lies on a segment from `a` to a point of the opposite side `bc`.
-/
lemma interior_reach {a b c p : Pts} (habc : noncol a b c)
    (hp : in_triang_interior p a b c) :
    ∃ d, in_closed_seg d b c ∧ between a p d := by
  -- By the crossbar theorem, there exists a point e on the ray from a to p that intersects bc.
  obtain ⟨e, he⟩ : ∃ e : Pts, e ∈ (a-ᵣp).inside ∧ e ∈ (b-ₛc).inside := by
    exact Hilbert.crossbar hp.1;
  -- Since $e \in (b-ₛc).inside$, we have $in_closed_seg e b c$.
  have h_closed : in_closed_seg e b c := by
    cases' he.2 with he₂ he₂;
    · exact Or.inr <| Or.inr he₂;
    · grind +locals;
  -- Since $e \in (a-ᵣp).inside$, we have $between a p e$.
  have h_between : between a p e ∨ between a e p ∨ between p a e := by
    apply Hilbert.between_tri;
    · apply in_ray_col;
      exact he.1;
    · obtain ⟨ _, _, _ ⟩ := hp;
      rename_i h₁ h₂ h₃;
      obtain ⟨ x, y, hxy ⟩ := h₂;
      grind +suggestions;
    · have h_not_in_line : a ∉ (b-ₗc) := by
        grind +suggestions;
      have h_not_in_line : e ∈ (b-ₛc).inside → e ∈ (b-ₗc) := by
        exact fun h => Hilbert.seg_in_line _ _ h;
      grind;
    · obtain ⟨h1, h2, h3⟩ := hp;
      have := Hilbert.same_side_line_notin ( Hilbert.inside_three_pt_ang.mp h2 |>.2 ) ; simp_all +decide ;
      exact fun h => this.2 <| h ▸ Hilbert.seg_in_line _ _ he.2;
  rcases h_between with ( h | h | h );
  · use e;
  · have := Hilbert.diff_side_pt_line ( show diff_side_pt e a p from by
                                          grind +suggestions ) ( Hilbert.line_in_lines ( show b ≠ c from by
                                                                                                            grind +suggestions ) ) ( show e ∈ ( b-ₗc ) from by
                                                                                                                                          exact Hilbert.seg_in_line _ _ he.2 ) ( show a ∉ ( b-ₗc ) from by
                                                                                                                                                                              grind +suggestions ) ( show p ∉ ( b-ₗc ) from by
                                                                                                                                                                                                                  have := hp.2.1; simp_all +decide [ inside_three_pt_ang ] ;
                                                                                                                                                                                                                  exact fun h => by have := this.2; exact absurd ( Hilbert.same_side_line_notin this ) ( by aesop ) ; ) ; simp_all +decide ;
    have := hp.2.1; simp_all +decide [ Hilbert.inside_three_pt_ang ] ;
    grind +suggestions;
  · have h_contradiction : a ∈ (p-ₛe).inside := by
      exact Or.inl h;
    have h_contradiction : same_side_pt a p e := by
      grind +suggestions;
    exact False.elim <| h_contradiction.1 ‹_›

/-
Every point of the closed triangle is `a`, lies on the closed side `bc`, or lies on a
segment from `a` to a point of the closed side `bc`.
-/
lemma reach_of_closed {a b c p : Pts} (habc : noncol a b c)
    (hp : in_closed_triang p a b c) :
    p = a ∨ in_closed_seg p b c ∨ ∃ d, in_closed_seg d b c ∧ between a p d := by
  rcases hp with ( hp | hp | hp | hp );
  · obtain rfl | rfl | hbp := hp <;> simp_all +decide [ in_closed_seg ];
  · exact Or.inr <| Or.inl hp;
  · grind +locals;
  · exact Or.inr <| Or.inr <| interior_reach habc hp

/-! ## Permutation invariance of closed-triangle membership -/

lemma in_closed_triang_perm12 {a b c p : Pts} (hp : in_closed_triang p a b c) :
    in_closed_triang p b a c := by
  revert hp;
  unfold in_closed_triang;
  unfold in_closed_seg in_triang_interior;
  grind +suggestions

lemma in_closed_triang_perm13 {a b c p : Pts} (hp : in_closed_triang p a b c) :
    in_closed_triang p c b a := by
  unfold in_closed_triang at *;
  unfold in_closed_seg at *; unfold in_triang_interior at *; simp_all +decide [ Hilbert.between_symm, Hilbert.ang_symm ] ;
  grind

/-! ## The two distance bounds -/

/-
The distance from a vertex `a` to any point `p` of the closed triangle is bounded by
the two sides adjacent to `a`.
-/
lemma vertex_to_pt {a b c p : Pts} (habc : noncol a b c)
    (hp : in_closed_triang p a b c) :
    ((a-ₛp) ≤ₛ (a-ₛb)) ∨ ((a-ₛp) ≤ₛ (a-ₛc)) := by
  obtain h|h|h := reach_of_closed habc hp;
  · exact Or.inl <| by simpa [ h ] using not_lt_degenerate
  · exact seg_le_max_of_closed_seg h
  · obtain ⟨d, hd_closed, hd_between⟩ := h
    have had_neq : a ≠ d := by
      grind +suggestions
    have had_proper : seg_proper (a-ₛd) := seg_proper_iff_neq.mpr had_neq
    obtain h|h := seg_le_max_of_closed_seg hd_closed;
    exact Or.inl <| seg_le_trans had_proper ( seg_lt_le <| sub_seg_lt hd_between ) h;
    exact Or.inr <| seg_le_trans had_proper ( seg_lt_le <| sub_seg_lt hd_between ) h

/-
The distance from any fixed point `o` to a point `p` of the closed triangle is bounded
by the distances from `o` to the three vertices.
-/
lemma cevian {a b c p : Pts} {o : Pts} (habc : noncol a b c)
    (hp : in_closed_triang p a b c) :
    ((o-ₛp) ≤ₛ (o-ₛa)) ∨ ((o-ₛp) ≤ₛ (o-ₛb)) ∨ ((o-ₛp) ≤ₛ (o-ₛc)) := by
  by_cases ho : o = p;
  · simp_all +decide [ seg_le ];
    exact Or.inl ( Hilbert.not_lt_degenerate );
  · rcases reach_of_closed habc hp with ( rfl | hp | ⟨ d, hd, hapd ⟩ );
    · exact Or.inl <| seg_le_refl _;
    · obtain h | h := seg_le_max_of_closed_seg ( o := o ) hp <;> tauto;
    · obtain h | h := seg_lt_max_of_between hapd ho;
      · exact Or.inl <| seg_lt_le h;
      · have := seg_le_max_of_closed_seg ( o := o ) hd;
        cases this <;> simp_all +decide [ seg_le ];
        · exact Or.inr <| Or.inl <| fun h' => ‹¬ ( o-ₛb ) <ₛ o-ₛd› <| seg_lt_trans h' h;
        · exact Or.inr <| Or.inr <| fun h' => ‹¬ ( o-ₛc ) <ₛ o-ₛd› <| seg_lt_trans h' h

/-! ## Main theorem -/

/-
**The diameter inequality (synthetic, neutral geometry).**
For a triangle `a b c` and two points `p q` of the closed triangle, the segment `pq` does
not exceed the longest side.
-/
theorem dist_le_max_side {a b c p q : Pts} (habc : noncol a b c)
    (hp : in_closed_triang p a b c) (hq : in_closed_triang q a b c) :
    ((p-ₛq) ≤ₛ (a-ₛb)) ∨ ((p-ₛq) ≤ₛ (b-ₛc)) ∨ ((p-ₛq) ≤ₛ (a-ₛc)) := by
  obtain hA | hB | hC := cevian (o := p) habc hq;
  · by_cases hp : p = a;
    · obtain hq | hq := vertex_to_pt habc hq <;> simp_all +decide;
    · obtain hA' | hA'' := vertex_to_pt habc ‹in_closed_triang p a b c›;
      · exact Or.inl <| seg_le_trans ( by rw [ seg_symm ] ; exact seg_proper_iff_neq.mpr <| by tauto ) ( by simpa [ seg_symm ] using hA ) hA';
      · exact Or.inr <| Or.inr <| seg_le_trans ( show seg_proper ( a-ₛp ) from by simpa [ seg_proper_iff_neq ] using Ne.symm hp ) ( by simpa only [ seg_symm ] using hA ) hA'';
  · by_cases hp : p = b;
    · grind +suggestions;
    · have hB' : seg_le (p-ₛb) (b-ₛa) ∨ seg_le (p-ₛb) (b-ₛc) := by
        grind +suggestions;
      cases' hB' with hB' hB';
      · have hB'' : seg_le (p-ₛq) (b-ₛa) := by
          apply seg_le_trans;
          exact seg_proper_iff_neq.mpr hp; all_goals assumption;
        exact Or.inl <| by simpa only [ seg_symm ] using hB'';
      · exact Or.inr <| Or.inl <| seg_le_trans ( by simpa [ seg_proper_iff_neq ] using hp ) hB hB';
  · by_cases hpc : p = c;
    · grind +suggestions;
    · have hpc_proper : seg_proper (c-ₛp) := by
        exact seg_proper_iff_neq.mpr ( Ne.symm hpc );
      cases' vertex_to_pt ( noncol13 habc ) ( in_closed_triang_perm13 hp ) with h h <;> simp_all +decide [ seg_symm ];
      · exact Or.inr <| Or.inl <| seg_le_trans hpc_proper hC h;
      · exact Or.inr <| Or.inr <| seg_le_trans hpc_proper hC h

/-- Restatement: `pq` is not strictly greater than all three sides simultaneously
(i.e. `pq ≤ max {ab, bc, ac}`). -/
theorem not_all_sides_lt {a b c p q : Pts} (habc : noncol a b c)
    (hp : in_closed_triang p a b c) (hq : in_closed_triang q a b c) :
    ¬ (((a-ₛb) <ₛ (p-ₛq)) ∧ ((b-ₛc) <ₛ (p-ₛq)) ∧ ((a-ₛc) <ₛ (p-ₛq))) := by
  rintro ⟨hab, hbc, hac⟩
  rcases dist_le_max_side habc hp hq with h | h | h
  · exact h hab
  · exact h hbc
  · exact h hac

end Hilbert