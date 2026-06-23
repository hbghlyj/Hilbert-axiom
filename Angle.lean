import RequestProject.Hilbert.Sidedness

/-!
# Rays, angles and the crossbar theorem (Hilbert's axioms, Group II continued)

Lean 4 port of the ray/angle layer, culminating in the crossbar theorem.
The angle `∠ a o b` (vertex `o`) is written `∠[a, o, b]` to avoid clashing with
Mathlib's `∠` notation.
-/

universe u

namespace Hilbert

open IncidenceGeometry IncidenceOrderGeometry

variable [B : IncidenceOrderGeometry]

/-- A ray: a vertex together with all points on the same side as some point `a`. -/
structure ray where
  vertex : Pts
  inside : Set Pts
  in_eq : ∃ a : Pts, inside = {x : Pts | same_side_pt vertex a x} ∪ {vertex}

/-- The ray from `o` through `a`. -/
def two_pt_ray (o a : Pts) : ray := ⟨o, {x : Pts | same_side_pt o a x} ∪ {o}, ⟨a, rfl⟩⟩

notation:100 a "-ᵣ" b => two_pt_ray a b

lemma two_pt_ray_vertex (o a : Pts) : (o-ᵣa).vertex = o := rfl

lemma ray_unique {r₁ r₂ : ray} (hr₁r₂ : r₁.vertex = r₂.vertex) :
    (∃ x : Pts, x ≠ r₁.vertex ∧ x ∈ r₁.inside ∩ r₂.inside) → r₁ = r₂ := by
      intro h
      obtain ⟨x, hx_ne, hx⟩ := h
      have h_eq : r₁.inside = r₂.inside := by
        -- By definition of ray, we know that r₁.inside = {x | same_side_pt r₁.vertex a₁ x} ∪ {r₁.vertex} and r₂.inside = {x | same_side_pt r₂.vertex a₂ x} ∪ {r₂.vertex}.
        obtain ⟨a₁, ha₁⟩ := r₁.in_eq
        obtain ⟨a₂, ha₂⟩ := r₂.in_eq
        simp_all +decide [ Set.ext_iff ];
        grind +suggestions
      exact (by
      cases r₁ ; cases r₂ ; aesop)

lemma ray_eq_same_side_pt {r : ray} {a : Pts}
    (har : a ∈ r.inside) (hao : a ≠ r.vertex) : r = (r.vertex-ᵣa) := by
      apply ray_unique;
      · rfl;
      · use a;
        simp_all +decide [ two_pt_ray ];
        exact ⟨ by
          simp +decide [ two_pt_seg, same_side_pt ];
          exact ⟨ Ne.symm hao, by rintro h; have := B.B1 h; tauto ⟩, by
          obtain ⟨ l, hl ⟩ := B.I1 ( show r.vertex ≠ a by tauto );
          exact ⟨ l, hl.1, hl.2.1, hl.2.2.1, hl.2.2.1 ⟩ ⟩

lemma ray_in_neq {o a b : Pts} (hbo : b ≠ o) (h : b ∈ (o-ᵣa).inside) : same_side_pt o a b := by
  cases h <;> simp_all +decide [ two_pt_ray ]

lemma two_pt_ray_eq_same_side_pt {o a b : Pts} (hoab : same_side_pt o a b) :
    (o-ᵣa) = (o-ᵣb) := by
      apply ray_unique;
      · rfl;
      · unfold two_pt_ray; simp_all +decide [ same_side_pt ] ;
        grind +suggestions

lemma ray_singleton (a : Pts) : (a-ᵣa).inside = {a} := by
  simp [Hilbert.two_pt_ray];
  simp +decide [ same_side_pt ];
  ext x; simp [Hilbert.two_pt_seg]

lemma in_ray_col {o a b : Pts} : b ∈ (o-ᵣa).inside → col o a b := by
  by_cases ho : o = a;
  · grind +suggestions;
  · -- If b is in the ray from o through a, then either b is the vertex o or b is on the same side of o as a.
    intro hb
    by_cases hb_vertex : b = o;
    · simp_all +decide [ col ];
      exact ⟨ _, B.I1 ho |> Classical.choose_spec |> And.left, B.I1 ho |> Classical.choose_spec |> And.right |> And.left, B.I1 ho |> Classical.choose_spec |> And.right |> And.right |> And.left, B.I1 ho |> Classical.choose_spec |> And.right |> And.left ⟩;
    · cases hb <;> simp_all +decide [ same_side_pt ]

lemma pt_left_in_ray (o a : Pts) : o ∈ (o-ᵣa).inside := by
  exact Set.mem_union_right _ ( Set.mem_singleton _ )

lemma pt_right_in_ray (o a : Pts) : a ∈ (o-ᵣa).inside := by
  unfold Hilbert.two_pt_ray;
  grind +suggestions

lemma seg_in_ray (o a : Pts) : (o-ₛa).inside ⊆ (o-ᵣa).inside := by
  -- If $x \in (o-ₛa).inside$, then $x$ is either $o$ or $a$, or between $o$ and $a$.
  intro x hx
  cases' hx with hx_o hx_a hx_between;
  · have := B.B1 hx_o; simp_all +decide [ between_same_side_pt ] ;
    exact Set.mem_union_left _ ( by tauto );
  · cases hx_a <;> simp_all +decide [ pt_left_in_ray, pt_right_in_ray ]

lemma ray_in_line (o a : Pts) : (o-ᵣa).inside ⊆ (o-ₗa) := by
  intro x hx
  by_cases hoa : o = a;
  · grind +suggestions;
  · convert Hilbert.col_in12 ( in_ray_col hx ) ( by tauto ) using 1

lemma t_shape_ray {a b c : Pts} (habc : noncol a b c) :
    ∀ {x : Pts}, same_side_pt b c x → same_side_line (a-ₗb) c x := by
      intro x hx;
      by_cases h : c = x <;> simp_all +decide [ same_side_line ];
      · simp_all +decide [ two_pt_seg, Set.Nonempty ];
        simp_all +decide [ Set.Nonempty, intersect ];
        grind +suggestions;
      · intro h';
        obtain ⟨ e, he ⟩ := h';
        -- Since $e$ is on the line $ab$ and $c$ and $x$ are on the same side of $b$, $e$ must be $b$.
        have he_eq_b : e = b := by
          have he_eq_b : e ∈ (a-ₗb) ∧ e ∈ (c-ₗx) := by
            exact ⟨ he.1, seg_in_line _ _ he.2 ⟩;
          have he_eq_b : b ∈ (a-ₗb) ∧ b ∈ (c-ₗx) := by
            have := hx.2; simp_all +decide [ same_side_pt ] ;
            obtain ⟨ l, hl₁, hl₂, hl₃, hl₄ ⟩ := this; simp_all +decide [ line ] ;
            grind +extAll;
          grind +suggestions;
        simp_all +decide [ same_side_pt ]

lemma t_shape_seg {a b c : Pts} (habc : noncol a b c) :
    ∀ x : Pts, between b x c → same_side_line (a-ₗb) c x :=
  fun _ hbxc => t_shape_ray habc (same_side_pt_symm (between_same_side_pt.1 hbxc).1)

lemma between_diff_side_line {o a b c : Pts} (hoab : noncol o a b) (hacb : between a c b) :
    diff_side_line (o-ₗc) a b := by
      refine' ⟨ _, _, _ ⟩;
      · use c;
        exact ⟨ Hilbert.pt_right_in_line _ _, by erw [ Hilbert.two_pt_seg ] ; exact Set.mem_union_left _ ( by simpa using hacb ) ⟩;
      · contrapose! hoab;
        unfold noncol;
        grind +suggestions;
      · contrapose! hoab;
        have h_col : col o a b := by
          have := B.B1 hacb;
          grind +suggestions;
        exact fun h => h h_col

lemma between_same_side_line {o a b c : Pts} (hoab : noncol o a b) (hacb : between a c b) :
    same_side_line (o-ₗa) b c := by
      convert Hilbert.t_shape_seg hoab c hacb using 1

lemma ray_same_side_line {o a b c b' : Pts} (hoa : o ≠ a) (h : same_side_line (o-ₗa) b c)
    (hobb' : same_side_pt o b b') : same_side_line (o-ₗa) b' c := by
      grind +suggestions

lemma ray_diff_side_line {o a b c a' : Pts} (hob : o ≠ b) (h : diff_side_line (o-ₗb) a c)
    (hoaa' : same_side_pt o a a') : diff_side_line (o-ₗb) a' c := by
      grind +suggestions

lemma diff_same_side_line' {a o b c : Pts} :
    diff_side_line (o-ₗb) a c → same_side_line (o-ₗa) b c → same_side_line (o-ₗc) a b := by
      intro h₁ h₂;
      have hoa := (diff_side_line_neq h₁).1.symm
      have hoc := (diff_side_line_neq' h₁).1.symm
      have hab := (diff_side_line_neq h₁).2
      have hob := (same_side_line_neq h₂).1.symm;
      cases' h₁ with h₁₁ h₁₂;
      -- Let $b'$ be a point on the segment $(a-ₛc)$ that lies on the line $(o-ₗb)$.
      obtain ⟨b', hb'⟩ : ∃ b', b' ∈ (a-ₛc).inside ∧ b' ∈ (line o b).val := by
        exact h₁₁.imp fun x hx => ⟨ hx.2, hx.1 ⟩;
      have hb'a : b' ≠ a := fun hf => h₁₂.1 (hf ▸ hb'.2)
      have hb'c : b' ≠ c := fun hf => h₁₂.2 (hf ▸ hb'.2)
      have hb'o : b' ≠ o := fun hf => (same_side_line_noncol h₂ hoa).2 (col_in23' ((seg_in_line a c) (hf ▸ hb'.1)));
      have hab'c := seg_in_neq hb'a hb'c hb'.1;
      apply same_side_line_symm; apply ray_same_side_line;
      exact hoc;
      apply same_side_line_symm; apply between_same_side_line;
      exact noncol23 ( same_side_line_noncol h₂ hoa ).2;
      exact B.B1 hab'c |>.1;
      have hobb' := col_in13' hb'.2;
      apply same_side_line_pt;
      exact hobb';
      exact line_in_lines hoa;
      · exact pt_left_in_line _ _;
      · grind +suggestions;
      · exact fun h => h₂ ⟨ b, h, by tauto ⟩;
      · apply same_side_line_symm; apply ray_same_side_line;
        exact hoa;
        apply same_side_line_trans (line_in_lines hoa) h₂;
        · apply t_shape_seg (same_side_line_noncol h₂ hoa).2 b' hab'c;
        · exact same_side_pt_refl ( by tauto )

/-- An angle: a vertex and an inside that is the union of two rays from the vertex. -/
structure ang where
  vertex : Pts
  inside : Set Pts
  in_eq : ∃ a b : Pts, inside = (vertex-ᵣa).inside ∪ (vertex-ᵣb).inside

/-- The angle `∠ a o b` with vertex `o`, written `∠[a, o, b]`. -/
def three_pt_ang (a o b : Pts) : ang := ⟨o, (o-ᵣa).inside ∪ (o-ᵣb).inside, ⟨a, b, rfl⟩⟩

notation:max "∠[" a ", " o ", " b "]" => three_pt_ang a o b

lemma ang_symm (a o b : Pts) : ∠[a, o, b] = ∠[b, o, a] := by
  unfold three_pt_ang;
  grind

lemma three_pt_ang_vertex (a o b : Pts) : (∠[a, o, b]).vertex = o := rfl

lemma pt_left_in_three_pt_ang (a o b : Pts) : a ∈ (∠[a, o, b]).inside := by
  exact Set.mem_union_left _ ( pt_right_in_ray _ _ )

lemma pt_right_in_three_pt_ang (a o b : Pts) : b ∈ (∠[a, o, b]).inside := by
  exact Set.mem_union_right _ ( pt_right_in_ray _ _ )

lemma ang_eq_same_side_pt (a : Pts) {o b c : Pts} (hobc : same_side_pt o b c) :
    ∠[a, o, b] = ∠[a, o, c] := by
      -- By definition of three_pt_ang, we have ∠[a, o, b] = (o-ₗa).inside ∪ (o-ₗb).inside and ∠[a, o, c] = (o-ₗa).inside ∪ (o-ₗc).inside.
      unfold three_pt_ang;
      grind +suggestions

/-- An angle is proper if its sides are non-collinear (its inside is in no single line). -/
def ang_proper (α : ang) : Prop := ∀ l ∈ Lines, ¬ α.inside ⊆ l

lemma ang_proper_iff_noncol {a o b : Pts} :
    ang_proper (∠[a, o, b]) ↔ noncol a o b := by
      constructor;
      · intro h;
        contrapose! h;
        obtain ⟨l, hl⟩ : ∃ l : Set Pts, l ∈ Lines ∧ a ∈ l ∧ o ∈ l ∧ b ∈ l := by
          exact Classical.not_not.1 h;
        exact fun h' => h' l hl.1 <| Set.union_subset ( Set.Subset.trans ( ray_in_line _ _ ) <| by
          by_cases hoa : o = a;
          · simp_all +decide [ line ];
          · grind +suggestions ) ( Set.Subset.trans ( ray_in_line _ _ ) <| by
          by_cases h : o = b <;> simp_all +decide [ line ];
          grind +qlia );
      · intro h_noncol l hl;
        contrapose! h_noncol;
        exact fun h => h ⟨ l, hl, h_noncol ( by exact Set.mem_union_left _ ( pt_right_in_ray _ _ ) ), h_noncol ( by exact Set.mem_union_left _ ( pt_left_in_ray _ _ ) ), h_noncol ( by exact Set.mem_union_right _ ( pt_right_in_ray _ _ ) ) ⟩

lemma three_pt_ang_eq_iff_prep {a o b a' b' : Pts} (haob : ang_proper (∠[a, o, b])) :
    (∠[a, o, b]) = (∠[a', o, b']) → same_side_pt o a a' → same_side_pt o b b' := by
      intro h_eq h_same_side;
      have h_b_in_angle : b' ∈ (three_pt_ang a o b).inside := by
        exact h_eq.symm ▸ pt_right_in_three_pt_ang _ _ _;
      by_cases h : b' = o <;> simp_all +decide [ three_pt_ang ];
      · contrapose! haob;
        unfold ang_proper; simp +decide [ same_side_pt ] ;
        use (o-ₗa');
        grind +suggestions;
      · have h_b_in_ray : b' ∈ (two_pt_ray o a).inside ∨ b' ∈ (two_pt_ray o b).inside := by
          exact h_eq.symm.subset h_b_in_angle;
        cases' h_b_in_ray with h_b_in_ray h_b_in_ray;
        · have h_b_in_ray : noncol a' o b' := by
            convert ang_proper_iff_noncol.mp haob using 1;
          have h_b_in_ray : col o a' b' := by
            grind +suggestions;
          grind +suggestions;
        · exact ray_in_neq h h_b_in_ray

lemma three_pt_ang_eq_iff {a o b a' o' b' : Pts} (haob : noncol a o b) :
    (∠[a, o, b]) = (∠[a', o', b']) ↔ o = o'
      ∧ ((same_side_pt o a a' ∧ same_side_pt o b b')
        ∨ (same_side_pt o a b' ∧ same_side_pt o b a')) := by
          constructor <;> intro h;
          · obtain ⟨h₁, h₂⟩ : o = o' := by
              injection h;
            have h₁ := @Hilbert.three_pt_ang_eq_iff_prep B a o b a' b' ?_;
            · have h₂ := @Hilbert.three_pt_ang_eq_iff_prep B a o b b' a' ?_ ?_ <;> simp_all +decide [ three_pt_ang ];
              · unfold two_pt_ray at h; simp_all +decide [ Set.ext_iff ] ;
                grind +suggestions;
              · convert ang_proper_iff_noncol.mpr haob using 1;
                convert ‹three_pt_ang a o b = three_pt_ang a' o b'›.symm using 1;
              · exact Set.union_comm _ _;
            · convert ang_proper_iff_noncol.mpr haob;
          · cases h.2 <;> simp_all +decide [ three_pt_ang ];
            · congr! 1;
              · have := ‹same_side_pt o' a a' ∧ same_side_pt o' b b'›.1; have := ‹same_side_pt o' a a' ∧ same_side_pt o' b b'›.2; simp_all +decide [ same_side_pt ] ;
                exact two_pt_ray_eq_same_side_pt ( by tauto ) ▸ rfl;
              · exact two_pt_ray_eq_same_side_pt ( by tauto ) ▸ rfl;
            · grind +suggestions

lemma ang_three_pt (α : ang) : ∃ a b : Pts, α = ∠[a, α.vertex, b] := by
  cases α ; aesop

/-- `p` is inside angle `α`: it is on the same side of each side-line as the opposite side. -/
def inside_ang (p : Pts) (α : ang) : Prop :=
  ∃ a b : Pts, α = ∠[a, α.vertex, b]
    ∧ same_side_line (α.vertex-ₗa) b p ∧ same_side_line (α.vertex-ₗb) a p

lemma inside_ang_proper {p : Pts} {α : ang} : inside_ang p α → ang_proper α := by
  intro hp
  obtain ⟨a, b, hα, hsm1, hsm2⟩ := hp
  have hcol : noncol a α.vertex b := by
    grind +suggestions;
  convert ang_proper_iff_noncol.mpr hcol

lemma inside_three_pt_ang {p a o b : Pts} :
    inside_ang p (∠[a, o, b]) ↔ same_side_line (o-ₗa) b p ∧ same_side_line (o-ₗb) a p := by
  constructor
  · intro hp
    have haob := inside_ang_proper hp
    obtain ⟨a', b', haoba'ob', hb'p, ha'p⟩ := hp
    rw [three_pt_ang_vertex] at haoba'ob' ha'p hb'p
    have ha'ob' : noncol a' o b' := by
      rw [haoba'ob', ang_proper_iff_noncol] at haob; exact haob
    rw [ang_proper_iff_noncol] at haob
    have hoa := (noncol_neq haob).1.symm
    have hoa' := (noncol_neq ha'ob').1.symm
    have hob := (noncol_neq haob).2.2
    have hob' := (noncol_neq ha'ob').2.2
    rcases ((three_pt_ang_eq_iff haob).1 haoba'ob').2 with h | h
    · constructor
      · rw [two_pt_one_line (line_in_lines hoa) (line_in_lines hoa') hoa
          (pt_left_in_line o a) (pt_right_in_line o a) (pt_left_in_line o a') (col_in13 h.1.2 hoa')]
        exact ray_same_side_line hoa' hb'p (same_side_pt_symm h.2)
      · rw [two_pt_one_line (line_in_lines hob) (line_in_lines hob') hob
          (pt_left_in_line o b) (pt_right_in_line o b) (pt_left_in_line o b') (col_in13 h.2.2 hob')]
        exact ray_same_side_line hob' ha'p (same_side_pt_symm h.1)
    · constructor
      · rw [two_pt_one_line (line_in_lines hoa) (line_in_lines hob') hoa
          (pt_left_in_line o a) (pt_right_in_line o a) (pt_left_in_line o b') (col_in13 h.1.2 hob')]
        exact ray_same_side_line hob' ha'p (same_side_pt_symm h.2)
      · rw [two_pt_one_line (line_in_lines hob) (line_in_lines hoa') hob
          (pt_left_in_line o b) (pt_right_in_line o b) (pt_left_in_line o a') (col_in13 h.2.2 hoa')]
        exact ray_same_side_line hoa' hb'p (same_side_pt_symm h.1)
  · rintro ⟨hap, hbp⟩
    exact ⟨a, b, rfl, hap, hbp⟩

lemma inside_ang_proper' {p a o b : Pts} : inside_ang p (∠[a, o, b])
    → ang_proper (∠[p, o, a]) ∧ ang_proper (∠[p, o, b]) := by
      intro h
      have h_noncol : noncol p o a ∧ noncol p o b := by
        have h_noncol_p : same_side_line (o-ₗa) b p ∧ same_side_line (o-ₗb) a p := by
          exact inside_three_pt_ang.mp h;
        grind +suggestions;
      exact ⟨ ang_proper_iff_noncol.mpr h_noncol.1, ang_proper_iff_noncol.mpr h_noncol.2 ⟩

lemma hypo_inside_ang {a b c d : Pts} (habc : noncol a b c) (hadc : between a d c) :
    inside_ang d (∠[a, b, c]) := by
      refine' ⟨ a, c, _, _, _ ⟩;
      · rfl;
      · convert t_shape_seg ( noncol12 habc ) d hadc using 1;
      · have := t_shape_seg ( noncol123 habc ) d ( B.B1 hadc |>.1 ) ; simp_all +decide [ same_side_line ] ;
        convert this using 1

/-- The crossbar theorem: a ray into the interior of an angle meets the opposite segment. -/
theorem crossbar {a b c d : Pts} (hd : inside_ang d (∠[b, a, c])) :
    (two_pt_ray a d).inside ♥ (b-ₛc).inside := by
  have hbac := inside_ang_proper hd
  rw [ang_proper_iff_noncol] at hbac
  have hab := (noncol_neq hbac).1.symm
  have hac := (noncol_neq hbac).2.2
  rw [inside_three_pt_ang] at hd
  have had := (same_side_line_neq' hd.1).1.symm
  have hacd := ((same_side_line_noncol hd.2) hac).2
  have habd := ((same_side_line_noncol hd.1) hab).2
  obtain ⟨e, hcae⟩ := between_extend hac.symm
  have hce := (between_neq hcae).2.1
  have hae := (between_neq hcae).2.2
  have hceb := col_noncol (between_col hcae) (noncol13 hbac) hce
  have haed := col_noncol (col12 (between_col hcae)) hacd hae
  have haeb := col_noncol (col12 (between_col hcae)) (noncol123 hbac) hae
  have hmeet : ((a-ₗd) ♥ (c-ₛe).inside) := ⟨a, pt_left_in_line a d, Or.inl hcae⟩
  rcases (pasch hceb (line_in_lines had) (noncol_in13 hacd) (noncol_in13 haed)
      (noncol_in13 habd) hmeet).1 with H | H
  · obtain ⟨x, hx⟩ := H
    have hxa : x ≠ a := fun hf => (noncol_in31 hbac) (hf ▸ (seg_in_line c b) hx.2)
    have hxb : x ≠ b := fun hf => (noncol_in13 habd) (hf ▸ hx.1)
    have hxc : x ≠ c := fun hf => (noncol_in13 hacd) (hf ▸ hx.1)
    rcases (line_separation (col_in12' hx.1) had.symm hxa).1 with h | h
    · rw [seg_symm b c]
      exact ⟨x, Or.inl h, hx.2⟩
    · have h₁ : diff_side_line (a-ₗc) d x :=
        diff_side_pt_line h (line_in_lines hac) (pt_left_in_line a c) (noncol_in12 hacd)
          (noncol_in13 (col_noncol (diff_side_pt_col h) (noncol23 hacd) hxa.symm))
      have h₂ : same_side_line (a-ₗc) d x :=
        same_side_line_symm (same_side_line_trans (line_in_lines hac)
          (same_side_line_symm (t_shape_seg (noncol123 hbac) x (seg_in_neq hxc hxb hx.2))) hd.2)
      exact absurd h₁ ((not_diff_side_line (noncol_in12 hacd) h₁.2.2).2 h₂)
  · obtain ⟨x, hx⟩ := H
    have hxa : x ≠ a := fun hf => (noncol_in23 haeb) (hf ▸ (seg_in_line e b) hx.2)
    have hxb : x ≠ b := fun hf => (noncol_in13 habd) (hf ▸ hx.1)
    have hxe : x ≠ e := fun hf => (noncol_in13 haed) (hf ▸ hx.1)
    rcases (line_separation (col_in12' hx.1) had.symm hxa).1 with h | h
    · have h₁ : same_side_line (a-ₗb) c x :=
        same_side_line_trans (line_in_lines hab) hd.1
          (by rw [line_symm]; exact t_shape_ray (noncol12 habd) h)
      have h₂ : diff_side_line (a-ₗb) c x :=
        diff_same_side_line (line_in_lines hab)
          (diff_side_pt_line (between_diff_side_pt.1 hcae) (line_in_lines hab)
            (pt_left_in_line a b) (noncol_in21 hbac) (noncol_in13 haeb))
          (t_shape_seg (noncol23 haeb) x (seg_in_neq hxb hxe (seg_symm e b ▸ hx.2)))
      exact absurd h₁ ((not_same_side_line (noncol_in21 hbac) (same_side_line_notin h₁).2).2 h₂)
    · have h₁ : diff_side_line (a-ₗc) d x :=
        diff_side_pt_line h (line_in_lines hac) (pt_left_in_line a c) (noncol_in12 hacd)
          (noncol_in13 (col_noncol (diff_side_pt_col h) (noncol23 hacd) hxa.symm))
      have h₂ : same_side_line (a-ₗc) d x := by
        apply same_side_line_trans (line_in_lines hac) (same_side_line_symm hd.2)
        rw [two_pt_one_line (line_in_lines hac) (line_in_lines hae) hac (pt_left_in_line a c)
          (pt_right_in_line a c) (pt_left_in_line a e) (col_in23 (between_col hcae) hae)]
        exact t_shape_seg haeb x (seg_in_neq hxe hxb hx.2)
      exact absurd h₁ ((not_diff_side_line (noncol_in12 hacd) h₁.2.2).2 h₂)

lemma ray_inside_ang {a o b p q : Pts} :
    inside_ang p (∠[a, o, b]) → same_side_pt o p q → inside_ang q (∠[a, o, b]) := by
      intro hpq;
      intro hq;
      obtain ⟨a', b', hab', hpq', hq'⟩ := hpq;
      refine' ⟨ a', b', hab', _, _ ⟩;
      · grind +suggestions;
      · grind +suggestions

/-- Two proper angles are supplementary if they share a ray and the others are opposite. -/
def supplementary (α β : ang) : Prop :=
  (∃ a b c d : Pts, α = ∠[b, a, c] ∧ β = ∠[b, a, d] ∧ between c a d)
    ∧ ang_proper α ∧ ang_proper β

lemma three_pt_ang_supplementary {a b c d : Pts} :
    supplementary (∠[b, a, c]) (∠[b, a, d]) ↔ between c a d ∧ noncol b a c ∧ noncol b a d := by
  constructor <;> rintro ⟨ h₁, h₂, h₃ ⟩;
  · obtain ⟨ a', b', c', d', h₁, h₂, h₃ ⟩ := h₁;
    have h₄ : between c' a d := by
      grind +suggestions
    have h₅ : between c a d := by
      grind +suggestions;
    exact ⟨ h₅, by simpa using ang_proper_iff_noncol.mp ‹ang_proper ( three_pt_ang b a c ) ›, by simpa using ang_proper_iff_noncol.mp ‹ang_proper ( three_pt_ang b a d ) › ⟩;
  · constructor;
    · use a, b, c, d;
    · exact ⟨ by simpa using ang_proper_iff_noncol.mpr ( by tauto ), by simpa using ang_proper_iff_noncol.mpr ( by tauto ) ⟩

lemma inside_ang_trans {a b c d e : Pts} :
    inside_ang d (∠[b, a, c]) → inside_ang e (∠[b, a, d]) → inside_ang e (∠[b, a, c]) := by
  intro hd he
  have hbac := ang_proper_iff_noncol.1 (inside_ang_proper hd)
  have hab := (noncol_neq hbac).1.symm
  have hac := (noncol_neq hbac).2.2
  obtain ⟨d', hd'⟩ := crossbar hd
  rw [inside_three_pt_ang] at hd
  have hd'a : d' ≠ a := fun hf => (noncol_in13 hbac) (hf ▸ (seg_in_line b c) hd'.2)
  have hd'b : d' ≠ b := fun hf =>
    (noncol_in13 (same_side_line_noncol hd.1 hab).2) (hf ▸ (ray_in_line a d) hd'.1)
  have hd'c : d' ≠ c := fun hf =>
    (noncol_in13 (same_side_line_noncol hd.2 hac).2) (hf ▸ (ray_in_line a d) hd'.1)
  have hadd' := ray_in_neq hd'a hd'.1
  have hbd'c := seg_in_neq hd'b hd'c hd'.2
  rw [ang_eq_same_side_pt b hadd'] at he
  obtain ⟨e', he'⟩ := crossbar he
  have he'a : e' ≠ a := fun hf =>
    noncol_in13 (ang_proper_iff_noncol.1 (inside_ang_proper he)) (hf ▸ (seg_in_line b d') he'.2)
  have he'b : e' ≠ b := fun hf =>
    noncol_in21 (ang_proper_iff_noncol.1 (inside_ang_proper' he).1) (hf ▸ (ray_in_line a e) he'.1)
  have he'd' : e' ≠ d' := fun hf =>
    noncol_in21 (ang_proper_iff_noncol.1 (inside_ang_proper' he).2) (hf ▸ (ray_in_line a e) he'.1)
  have haee' := ray_in_neq he'a he'.1
  have hbe'c := seg_in_neq he'b he'd' he'.2
  apply ray_inside_ang _ (same_side_pt_symm haee')
  apply hypo_inside_ang hbac
  rw [between_symm] at hbd'c hbe'c
  rw [between_symm]
  exact (between_trans' hbd'c hbe'c).2

lemma inside_ang_trans' {a o b c d : Pts} (hboc : between b o c) :
    inside_ang d (∠[a, o, b]) → inside_ang a (∠[d, o, c]) := by
      intro hd
      rw [inside_three_pt_ang] at hd;
      constructor;
      have h₁ : diff_side_line (o-ₗd) a b := by
        have h₁ : (two_pt_ray o d).inside ♥ (a-ₛb).inside := by
          apply crossbar;
          exact ⟨ a, b, rfl, hd.1, hd.2 ⟩;
        refine' ⟨ _, _, _ ⟩;
        · obtain ⟨ x, hx ⟩ := h₁;
          exact ⟨ x, ray_in_line _ _ hx.1, hx.2 ⟩;
        · grind +suggestions;
        · convert h₁ using 1; all_goals grind +suggestions
      have h₂ : diff_side_line (o-ₗd) b c := by
        apply diff_side_pt_line (between_diff_side_pt.1 hboc) (line_in_lines (by
        grind +suggestions)) (pt_left_in_line o d) (by
        grind +suggestions) (by
        have := same_side_line_noncol hd.2 (by
        have := B.B1 hboc; aesop;);
        have := col_noncol ( col12 ( between_col hboc ) ) this.2 ( by
          exact fun h => by have := B.B3.2 b o c; aesop; )
        generalize_proofs at *;
        exact noncol_in13 this)
      have h₃ : same_side_line (o-ₗd) a c := by
        grind +suggestions;
      use c;
      use rfl;
      convert And.intro ( same_side_line_symm h₃ ) ( same_side_line_symm hd.2 ) using 1;
      convert Iff.rfl using 2;
      apply two_pt_one_line;
      grind +suggestions;
      exact line_in_lines ( by
        grind +suggestions );
      rotate_left;
      exact pt_left_in_line o b;
      exact pt_right_in_line o b;
      · exact ray_in_line _ _ ( by tauto );
      · exact col_in23 ( between_col hboc ) ( by
          grind +suggestions );
      · exact fun h => by have := B.B3.2 b o c; aesop;

end Hilbert