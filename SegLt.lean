import RequestProject.Hilbert.Congruence

/-!
# Segment ordering (Hilbert's axioms, Group III continued)

Lean 4 port of the segment-orderness layer: `seg_lt` (written `<ₛ`), with congruence,
transitivity and trichotomy.
-/

universe u

namespace Hilbert

open IncidenceGeometry IncidenceOrderGeometry HilbertPlane

variable [C : HilbertPlane]

/-- Segment `m` is less than segment `n` if a proper part of `n` is congruent to `m`:
there is a point `a` strictly between the endpoints `b`, `c` of `n` with `m ≅ₛ (b-ₛa)`. -/
def seg_lt (m n : seg) : Prop :=
  ∃ a b c : Pts, n = (b-ₛc) ∧ between b a c ∧ (m ≅ₛ (b-ₛa))

@[inherit_doc] notation:50 a " <ₛ " b => seg_lt a b

lemma seg_lt_proper {m n : seg} : (m <ₛ n) → seg_proper n := by
  intro h
  obtain ⟨a, b, c, hn, hbac⟩ := h;
  obtain ⟨l, hl⟩ := C.B1 hbac.left;
  exact hn.symm ▸ seg_proper_iff_neq.mpr hl.2.1

lemma two_pt_seg_lt {m : seg} {a b : Pts} :
    (m <ₛ (a-ₛb)) ↔ ∃ x : Pts, between a x b ∧ (m ≅ₛ (a-ₛx)) := by
      constructor <;> intro h;
      · obtain ⟨x, a', b', haba'b', ha'xb', hm⟩ := h
        rcases two_pt_seg_pt haba'b' with hcase | hcase
        · -- hcase : a = a' ∧ b = b'
          rw [← hcase.1, ← hcase.2] at ha'xb'
          rw [← hcase.1] at hm
          exact ⟨x, ha'xb', hm⟩
        · -- hcase : a = b' ∧ b = a'
          obtain ⟨y, haby, hy, -⟩ := extend_congr_seg (seg_proper_iff_neq.2 (between_neq ha'xb').1) (by
          grind +suggestions : b' ≠ a')
          generalize_proofs at *;
          have := congr_seg_sub ha'xb' ( same_side_pt_symm haby ) hy ( by rw [ seg_symm ] ; exact seg_congr_refl _ );
          grind +suggestions;
      · unfold seg_lt; aesop;

lemma seg_lt_congr {m n l : seg} (hmn : m ≅ₛ n) :
    ((m <ₛ l) → (n <ₛ l)) ∧ (seg_proper n → (l <ₛ m) → (l <ₛ n)) := by
      constructor;
      · rintro ⟨ a, b, c, hl, hbac, hm ⟩;
        grind +suggestions;
      · rintro hn ⟨ a, b, c, hlbc, hbac, hm ⟩;
        obtain ⟨ d, e, hnde ⟩ := Hilbert.seg_two_pt n;
        rw [ hnde, seg_proper_iff_neq ] at hn;
        obtain ⟨ x, hdex, hx ⟩ := Hilbert.extend_congr_seg ( show seg_proper ( b-ₛa ) from by
                                                              exact seg_proper_iff_neq.mpr ( by have := C.B1 hbac; aesop ) ) hn;
        grind +suggestions

lemma seg_lt_trans {m n l : seg} : (m <ₛ n) → (n <ₛ l) → (m <ₛ l) := by
  intro hmn hnl
  obtain ⟨a, b, c, hl, hbac, hn⟩ := hnl
  have hab := (by
  exact ( Hilbert.between_neq hbac ).1.symm : a ≠ b)
  have hmn' := (seg_lt_congr hn).2 (seg_proper_iff_neq.2 hab.symm) hmn
  rw [two_pt_seg_lt] at hmn'
  obtain ⟨x, hbxa, hm⟩ := hmn'
  rw [hl, two_pt_seg_lt]
  refine ⟨x, ?_, hm⟩
  rw [between_symm] at hbac hbxa ⊢
  exact (Hilbert.between_trans' hbac hbxa).2

lemma seg_congr_same_side_unique {a b c d : Pts}
    (habc : same_side_pt a b c) (habd : same_side_pt a b d) :
    ((a-ₛc) ≅ₛ (a-ₛd)) → c = d := by
      grind +suggestions

lemma seg_tri {m n : seg} (ha'b' : seg_proper m) (hab : seg_proper n) :
    ((m <ₛ n) ∨ (m ≅ₛ n) ∨ (n <ₛ m))
      ∧ ¬((m <ₛ n) ∧ (m ≅ₛ n)) ∧ ¬((m <ₛ n) ∧ (n <ₛ m)) ∧ ¬((m ≅ₛ n) ∧ (n <ₛ m)) := by
      obtain ⟨a, b, hn⟩ := seg_two_pt n
      rw [hn, seg_proper_iff_neq] at hab
      obtain ⟨c, habc, hm, -⟩ := extend_congr_seg ha'b' hab
      have h₁ : (m <ₛ n) ↔ same_side_pt b a c := by
        rw [hn, two_pt_seg_lt]
        constructor
        · rintro ⟨c', hac'b, hm'⟩
          rw [between_same_side_pt] at hac'b
          have hcc' : c = c' :=
            seg_congr_same_side_unique habc (same_side_pt_symm hac'b.1)
              (seg_congr_trans (seg_congr_symm hm) hm')
          rw [hcc']; exact hac'b.2
        · intro hbac
          exact ⟨c, between_same_side_pt.2 ⟨same_side_pt_symm habc, hbac⟩, hm⟩
      have h₂ : (m ≅ₛ n) ↔ c = b := by
        rw [hn]
        constructor
        · intro hm'
          exact seg_congr_same_side_unique habc (same_side_pt_refl hab)
            (seg_congr_trans (seg_congr_symm hm) hm')
        · intro hcb; rw [hcb] at hm; exact hm
      have h₃ : (n <ₛ m) ↔ diff_side_pt b a c := by
        rw [hn]
        constructor
        · intro hnm
          replace hnm := (seg_lt_congr hm).2 (seg_proper_iff_neq.2 (same_side_pt_neq habc).2.symm) hnm
          rw [two_pt_seg_lt] at hnm
          obtain ⟨d, hadc, habad⟩ := hnm
          rw [seg_congr_same_side_unique (same_side_pt_symm habc)
            (same_side_pt_symm (between_same_side_pt.1 hadc).1) habad]
          rw [← between_diff_side_pt]; exact hadc
        · intro hbac
          apply (seg_lt_congr (seg_congr_symm hm)).2 ha'b'
          rw [two_pt_seg_lt]
          exact ⟨b, between_diff_side_pt.2 hbac, seg_congr_refl _⟩
      rw [h₁, h₂, h₃]
      refine ⟨?_, ?_, ?_, ?_⟩
      · by_cases hbc : b = c
        · right; left; exact hbc.symm
        · rcases (line_separation (col12 habc.2) hab (Ne.symm hbc)).1 with h | h
          · left; exact h
          · right; right; exact h
      · intro hf; exact (same_side_pt_neq hf.1).2 hf.2
      · intro hf
        rw [← not_diff_side_pt (col12 habc.2) hab hf.2.2.2] at hf
        exact hf.1 hf.2
      · intro hf; exact hf.2.2.2 hf.1

end Hilbert