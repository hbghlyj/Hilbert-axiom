import RequestProject.Hilbert.Congruence

/-!
# Angle ordering (Hilbert's axioms, Group III continued)

Lean 4 port of the angle-orderness layer: `ang_lt` (written `<ₐ`), with congruence,
transitivity and trichotomy.
-/

universe u

namespace Hilbert

open IncidenceGeometry IncidenceOrderGeometry HilbertPlane

variable [C : HilbertPlane]

/-- Angle `α` is less than `β` if a part of `β` is congruent to `α`: there is a point `p`
inside `β = ∠[a, o, b]` (vertex `o`) such that `∠[a, o, p] ≅ₐ α`. -/
def ang_lt (α β : ang) : Prop :=
  ∃ a b p : Pts, β = (∠[a, β.vertex, b]) ∧ inside_ang p (∠[a, β.vertex, b])
    ∧ ((∠[a, β.vertex, p]) ≅ₐ α)

@[inherit_doc] notation:50 a " <ₐ " b => ang_lt a b

lemma three_pt_ang_lt {a o b : Pts} {α : ang} :
    (α <ₐ (∠[a, o, b])) ↔ ∃ p : Pts, inside_ang p (∠[a, o, b]) ∧ ((∠[a, o, p]) ≅ₐ α) := by
      constructor <;> intro h_α_lt;
      · obtain ⟨a', b', p, haoba'ob', hp, ha'op⟩ := h_α_lt
        have ha'ob' := ang_proper_iff_noncol.1 (Hilbert.inside_ang_proper hp)
        have haob : noncol a o b := by
          rw [ ← Hilbert.ang_proper_iff_noncol ] at *;
          grind
        have hoa := (noncol_neq haob).1.symm
        rcases ((three_pt_ang_eq_iff ha'ob').1 haoba'ob'.symm).2 with h | h;
        · use p;
          grind +suggestions;
        · obtain ⟨q, ha'opqoa, hqb, -⟩ := extend_congr_ang (Hilbert.inside_ang_proper' hp).1 hoa (Hilbert.noncol_in12 (Hilbert.noncol12 haob));
          refine' ⟨ q, _, _ ⟩;
          · convert congr_ang_sub hp hqb ( same_side_pt_neq h.2 ).2.symm _ _ |>.1 using 1;
            · exact haoba'ob'.symm ▸ ang_congr_refl _;
            · grind +suggestions;
          · grind +suggestions;
      · exact ⟨ a, b, h_α_lt.choose, rfl, h_α_lt.choose_spec.1, h_α_lt.choose_spec.2 ⟩

lemma ang_lt_congr {α β γ : ang} (hαβ : α ≅ₐ β) :
    ((α <ₐ γ) → (β <ₐ γ)) ∧ (ang_proper β → (γ <ₐ α) → (γ <ₐ β)) := by
      obtain ⟨a₁, b₁, hα⟩ := Hilbert.ang_three_pt α
      obtain ⟨a₂, b₂, hβ⟩ := Hilbert.ang_three_pt β
      obtain ⟨a₃, b₃, hγ⟩ := Hilbert.ang_three_pt γ
      rw [hα, hβ, hγ]; rw [hα, hβ] at hαβ
      constructor
      · intro hαγ
        obtain ⟨p, hpin, hp⟩ := Hilbert.three_pt_ang_lt.1 hαγ
        rw [Hilbert.three_pt_ang_lt]
        exact ⟨p, hpin, Hilbert.ang_congr_trans hp hαβ⟩
      · intro h hγα
        obtain ⟨p, hpin, hp⟩ := Hilbert.three_pt_ang_lt.1 hγα
        rw [Hilbert.ang_proper_iff_noncol] at h
        obtain ⟨q, hq, hqb₂, -⟩ := Hilbert.extend_congr_ang (Hilbert.inside_ang_proper' hpin).1 (Hilbert.noncol_neq h).1.symm (Hilbert.noncol_in12 (Hilbert.noncol12 h))
        rw [Hilbert.three_pt_ang_lt]
        rw [Hilbert.ang_symm q _ _] at hq
        refine ⟨q, (Hilbert.congr_ang_sub hpin hqb₂ (Hilbert.noncol_neq h).1.symm hαβ (by rw [Hilbert.ang_symm]; exact hq)).1, ?_⟩
        rw [Hilbert.ang_symm] at hq
        exact Hilbert.ang_congr_trans (Hilbert.ang_congr_symm hq) hp

lemma ang_lt_trans {α β γ : ang} :
    ang_proper α → (α <ₐ β) → (β <ₐ γ) → (α <ₐ γ) := by
      intro hα hαβ hβγ;
      obtain ⟨a₂, b₂, hβ⟩ := ang_three_pt β
      obtain ⟨a₃, b₃, hγ⟩ := ang_three_pt γ
      rw [hγ]; rw [hβ] at hαβ; rw [hβ, hγ] at hβγ
      generalize_proofs at *;
      obtain ⟨p, hpin, hp⟩ := three_pt_ang_lt.1 hαβ
      obtain ⟨q, hqin, hq⟩ := three_pt_ang_lt.1 hβγ
      have ha₃o₃b₃ := ang_proper_iff_noncol.1 (inside_ang_proper hqin)
      obtain ⟨x, hx, hxq, -⟩ := extend_congr_ang hα (noncol_neq ha₃o₃b₃).1.symm (noncol_in23 (ang_proper_iff_noncol.1 (inside_ang_proper' hqin).1))
      rw [three_pt_ang_lt]
      refine ⟨x, inside_ang_trans hqin ?_, ?_⟩
      · refine (congr_ang_sub hpin hxq (noncol_neq (ang_proper_iff_noncol.1 (inside_ang_proper hqin))).1.symm (ang_congr_symm hq) ?_).1
        rw [ang_symm] at hx; exact ang_congr_trans hp hx
      · rw [ang_symm]; exact ang_congr_symm hx

lemma ang_tri {α β : ang} (ha'o'b' : ang_proper α) (haob : ang_proper β) :
    ((α <ₐ β) ∨ (α ≅ₐ β) ∨ (β <ₐ α))
      ∧ ¬((α <ₐ β) ∧ (α ≅ₐ β)) ∧ ¬((α <ₐ β) ∧ (β <ₐ α)) ∧ ¬((α ≅ₐ β) ∧ (β <ₐ α)) := by
      obtain ⟨a, b, hβ⟩ := ang_three_pt β
      rw [hβ, ang_proper_iff_noncol] at haob
      set o := β.vertex with ho
      have hao := (noncol_neq haob).1
      have hbo := (noncol_neq haob).2.2.symm
      obtain ⟨x, hx, hlxb, hu⟩ := extend_congr_ang ha'o'b' hao.symm (noncol_in12 (noncol12 haob))
      have hxo := (same_side_line_neq hlxb).1
      have h₁ : same_side_line (o-ₗb) x a ↔ (α <ₐ β) := by
        rw [hβ]
        constructor
        · intro h₁
          rw [three_pt_ang_lt]
          exact ⟨x, inside_three_pt_ang.2 ⟨same_side_line_symm hlxb, same_side_line_symm h₁⟩,
            by rw [ang_symm]; exact ang_congr_symm hx⟩
        · rw [three_pt_ang_lt]
          rintro ⟨y, hyin, hy⟩
          rw [inside_three_pt_ang] at hyin; rw [ang_symm] at hy
          have hu' := hu y (same_side_line_trans (line_in_lines hao.symm) hlxb hyin.1)
            (ang_congr_symm hy)
          have hoxb := col_noncol (col_in13' ((ray_in_line o x) hu'))
            (noncol23 (same_side_line_noncol hyin.2 hbo.symm).2) hxo.symm
          have hyo := (same_side_line_neq' hyin.1).1
          apply same_side_line_trans (line_in_lines hbo.symm) _ (same_side_line_symm hyin.2)
          rw [line_symm]
          exact t_shape_ray (noncol132 hoxb) (ray_in_neq hyo hu')
      have h₂ : x ∈ (o-ₗb) ↔ (α ≅ₐ β) := by
        rw [hβ]
        constructor
        · intro h₂
          have hthis : (∠[x, o, a]) = (∠[a, o, b]) := by
            rw [ang_symm]
            apply ang_eq_same_side_pt
            rcases (line_separation ⟨(o-ₗb), line_in_lines hbo.symm, pt_left_in_line o b, h₂,
              pt_right_in_line o b⟩ hxo hbo).1 with h | h
            · exact h
            · have hx' := (same_side_line_notin hlxb).1
              have hb' := (same_side_line_notin hlxb).2
              rw [← not_diff_side_line hx' hb'] at hlxb
              exact absurd (diff_side_pt_line h (line_in_lines hao.symm) (pt_left_in_line o a)
                hx' hb') hlxb
          rw [← hthis]; exact hx
        · intro h₂
          rw [line_symm] at hlxb; rw [ang_symm] at hx
          exact col_in13 (ang_unique_same_side hao hlxb
            (ang_congr_trans (ang_congr_symm hx) h₂)).2 hbo.symm
      have h₃ : diff_side_line (o-ₗb) x a ↔ (β <ₐ α) := by
        constructor
        · intro h₃
          apply (ang_lt_congr (ang_congr_symm hx)).2 ha'o'b'
          rw [ang_symm, three_pt_ang_lt]
          exact ⟨b, inside_three_pt_ang.2 ⟨hlxb,
            diff_same_side_line' (diff_side_line_symm h₃) (same_side_line_symm hlxb)⟩,
            by rw [hβ]; exact ang_congr_refl _⟩
        · intro h₃
          have hxoa : ang_proper (∠[x, o, a]) := by
            rw [ang_proper_iff_noncol]; intro hxoa
            exact (same_side_line_notin hlxb).1 (col_in23 hxoa hao.symm)
          have hthis := (ang_lt_congr hx).2 hxoa h₃
          rw [ang_symm, three_pt_ang_lt] at hthis
          obtain ⟨p, hpin, hp⟩ := hthis
          rw [hβ] at hp
          have hopb : same_side_pt o p b := by
            rw [inside_three_pt_ang] at hpin
            rw [line_symm] at hpin hlxb
            exact ang_unique_same_side hao
              (same_side_line_trans (line_in_lines hao) (same_side_line_symm hpin.1) hlxb) hp
          have hbin := ray_inside_ang hpin hopb
          obtain ⟨y, hy⟩ := crossbar hbin
          rw [seg_symm] at hy
          refine ⟨⟨y, (ray_in_line o b) hy.1, hy.2⟩, ?_, ?_⟩
          · rw [inside_three_pt_ang] at hbin
            exact noncol_in13 (same_side_line_noncol hbin.2 hxo.symm).2
          · exact noncol_in23 haob
      rw [← h₁, ← h₂, ← h₃]
      refine ⟨?_, ?_, ?_, ?_⟩
      · by_cases hxob : x ∈ (o-ₗb)
        · right; left; exact hxob
        · rcases (plane_separation hxob (noncol_in23 haob)).1 with h | h
          · left; exact h
          · right; right; exact h
      · intro hf; exact (same_side_line_notin hf.1).1 hf.2
      · intro hf
        rw [← not_diff_side_line hf.2.2.1 hf.2.2.2] at hf
        exact hf.1 hf.2
      · intro hf; exact hf.2.2.1 hf.1

lemma ang_lt_supplementary {α α' β β' : ang} (hαα' : α <ₐ α')
    (hαβ : supplementary α β) (hα'β' : supplementary α' β') : β' <ₐ β := by
      have hαβ2 := hαβ
      obtain ⟨⟨a, b, c, d, hα, hβ, hcad⟩, hbac, hbad⟩ := hαβ
      rw [hβ] at hbad
      obtain ⟨⟨a', b', c', d', hα', hβ', hc'a'd'⟩, hb'a'c', hb'a'd'⟩ := hα'β'
      rw [hα', ang_proper_iff_noncol] at hb'a'c'
      rw [hβ', ang_proper_iff_noncol] at hb'a'd'
      rw [hβ, hβ']; rw [hα, hα'] at hαα'
      rw [hα, hβ] at hαβ2
      rw [ang_symm b' a' c'] at hαα'
      obtain ⟨e', he', hc'a'e'bac⟩ := three_pt_ang_lt.1 hαα'
      have ha'c' := (noncol_neq hb'a'c').2.2
      have ha'd' := (noncol_neq hb'a'd').2.2
      have ha'c'e' := (same_side_line_noncol (inside_three_pt_ang.1 he').1 ha'c').2
      have ha'd'e' := col_noncol (col12 (between_col hc'a'd')) ha'c'e' ha'd'
      have hsup : supplementary (∠[e', a', c']) (∠[e', a', d']) := by
        rw [three_pt_ang_supplementary]
        exact ⟨hc'a'd', noncol132 ha'c'e', noncol132 ha'd'e'⟩
      rw [ang_symm] at hc'a'e'bac
      have hbade'a'd' := supplementary_congr hαβ2 hsup (ang_congr_symm hc'a'e'bac)
      apply (ang_lt_congr (ang_congr_symm hbade'a'd')).2 hbad
      rw [ang_symm e' a' d', three_pt_ang_lt]
      refine ⟨b', ?_, by rw [ang_symm]; exact ang_congr_refl _⟩
      rw [ang_symm]
      apply inside_ang_trans' hc'a'd'
      rw [ang_symm]; exact he'

end Hilbert