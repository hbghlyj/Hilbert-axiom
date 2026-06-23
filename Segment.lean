import RequestProject.Hilbert.Incidence

/-!
# Order (betweenness) and segments (Hilbert's axioms, Group II)

Lean 4 port of the order layer: betweenness axioms B1–B4 (B4 = Pasch), segments, and the
derived Pasch theorem.
-/

universe u

namespace Hilbert

open IncidenceGeometry

/-- An incidence order geometry: an incidence geometry with a betweenness relation
`between a b c` ("`b` is between `a` and `c`") satisfying axioms B1–B4. -/
class IncidenceOrderGeometry extends IncidenceGeometry where
  between : Pt → Pt → Pt → Prop
  B1 : ∀ {a b c : Pt}, between a b c → between c b a
    ∧ (a ≠ b) ∧ (a ≠ c) ∧ (b ≠ c) ∧ col a b c
  B2 : ∀ {a b : Pt}, a ≠ b → ∃ c : Pt, between a b c
  B3 : (∀ {a b c : Pt} {l : Set Pt}, l ∈ lines → a ∈ l ∧ b ∈ l ∧ c ∈ l →
      (a ≠ b → a ≠ c → b ≠ c → between a b c ∨ between a c b ∨ between b a c)) ∧
    ∀ a b c : Pt, ¬(between a b c ∧ between b a c)
      ∧ ¬(between a b c ∧ between a c b) ∧ ¬(between b a c ∧ between a c b)
  B4 : ∀ {a b c : Pt} (l : Set Pt), l ∈ lines →
      (noncol a b c) → a ∉ l → b ∉ l → c ∉ l
      → (∃ d : Pt, between a d b ∧ d ∈ l) →
      (∃ p : Pt, p ∈ l ∧ (between a p c ∨ between b p c))
      ∧ ∀ p q : Pt, p ∈ l → q ∈ l → ¬(between a p c ∧ between b q c)

variable [B : IncidenceOrderGeometry]

open IncidenceOrderGeometry

lemma between_symm (a b c : Pts) : between a b c ↔ between c b a :=
  ⟨fun h => (B1 h).1, fun h => (B1 h).1⟩

lemma between_neq {a b c : Pts} (h : between a b c) : (a ≠ b) ∧ (a ≠ c) ∧ (b ≠ c) :=
  ⟨(B1 h).2.1, (B1 h).2.2.1, (B1 h).2.2.2.1⟩

lemma between_col {a b c : Pts} (h : between a b c) : col a b c := (B1 h).2.2.2.2

lemma between_extend {a b : Pts} (h : a ≠ b) : ∃ c : Pts, between a b c := B2 h

lemma between_tri {a b c : Pts} (habc : col a b c) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : between a b c ∨ between a c b ∨ between b a c := by
  obtain ⟨l, hl, h⟩ := habc; exact B3.1 hl ⟨h.1, h.2.1, h.2.2⟩ hab hac hbc

lemma between_contra {a b c : Pts} :
    ¬(between a b c ∧ between b a c)
    ∧ ¬(between a b c ∧ between a c b)
    ∧ ¬(between b a c ∧ between a c b) := B3.2 a b c

/-- A segment: a set of points consisting of two endpoints and the points between them. -/
structure seg where
  inside : Set Pts
  in_eq : ∃ a b : Pts, inside = {x : Pts | between a x b} ∪ {a, b}

/-- The segment with endpoints `a` and `b`. -/
def two_pt_seg (a b : Pts) : seg := ⟨{x : Pts | between a x b} ∪ {a, b}, ⟨a, b, rfl⟩⟩

notation:100 a "-ₛ" b => two_pt_seg a b

/-- A segment is proper when its inside is not a singleton (endpoints distinct). -/
def seg_proper (s : seg) : Prop := ∀ x : Pts, s.inside ≠ {x}

lemma pt_left_in_seg (a b : Pts) : a ∈ (a-ₛb).inside := by
  unfold two_pt_seg; simp

lemma pt_right_in_seg (a b : Pts) : b ∈ (a-ₛb).inside := by
  unfold two_pt_seg; simp

lemma seg_symm (a b : Pts) : (a-ₛb) = (b-ₛa) := by
  simp +decide [ two_pt_seg ];
  ext x; simp +decide [ Set.ext_iff, between_symm ] ;
  tauto

lemma seg_singleton (a : Pts) : (a-ₛa).inside = {a} := by
  ext x
  simp [two_pt_seg];
  grind +suggestions

lemma seg_proper_iff_neq {a b : Pts} : seg_proper (a-ₛb) ↔ a ≠ b := by
  constructor <;> intro h <;> contrapose! h;
  · unfold seg_proper;
    simp +decide [ h, two_pt_seg ];
    use b; ext x; simp [B.B1];
    intro hx; have := B.B1 hx; aesop;
  · obtain ⟨ x, hx ⟩ := not_forall.mp h;
    simp_all +decide [ Set.eq_singleton_iff_unique_mem, two_pt_seg ]

lemma seg_in_line (a b : Pts) : (a-ₛb).inside ⊆ (a-ₗb) := by
  intro c hc;
  by_cases h : a = b <;> simp_all +decide [ two_pt_seg ];
  · grind +suggestions;
  · rcases hc with ( rfl | rfl | hc );
    · grind;
    · grind +suggestions;
    · have := B.B1 hc; have := this.2.2.2; simp_all +decide [ col_in13 ] ;

lemma seg_two_pt (s : seg) : ∃ a b : Pts, s = (a-ₛb) := by
  rcases s with ⟨ s, ⟨ a, b, h ⟩ ⟩;
  exact ⟨ a, b, by unfold two_pt_seg; aesop ⟩

lemma seg_in_neq {a b x : Pts} (hxa : x ≠ a) (hxb : x ≠ b) (hx : x ∈ (a-ₛb).inside) :
    between a x b := by
      cases hx <;> simp_all +decide [ Set.ext_iff ]

/-
Pasch's theorem, rephrasing B4 in terms of segments.
-/
theorem pasch {a b c : Pts} (habc : noncol a b c) {l : Set Pts} (hl : l ∈ Lines)
    (hal : a ∉ l) (hbl : b ∉ l) (hcl : c ∉ l) (hlab : l ♥ (a-ₛb).inside) :
    ((l ♥ (a-ₛc).inside) ∨ (l ♥ (b-ₛc).inside))
      ∧ ¬((l ♥ (a-ₛc).inside) ∧ (l ♥ (b-ₛc).inside)) := by
        obtain ⟨ d, hd ⟩ := hlab;
        obtain ⟨ p, hp ⟩ := B.B4 l hl habc hal hbl hcl ⟨ d, by
          cases eq_or_ne d a <;> cases eq_or_ne d b <;> simp_all +decide [ two_pt_seg ] ⟩;
        refine' ⟨ _, _ ⟩;
        · rcases p with ⟨ p, hp₁, hp₂ | hp₂ ⟩ <;> [ left; right ] <;> refine' ⟨ p, hp₁, _ ⟩ <;> simp_all +decide [ two_pt_seg ];
        · simp_all +decide [ Set.Nonempty ];
          rintro ⟨ x, hx ⟩ ⟨ y, hy ⟩;
          grind +locals

lemma two_pt_between {a b : Pts} (hab : a ≠ b) : ∃ c : Pts, between a c b := by
  obtain ⟨c, habc⟩ := noncol_exist hab
  have hac := (noncol_neq habc).2.1
  obtain ⟨d, hacd⟩ := between_extend hac
  have had := (between_neq hacd).2.1
  have hcd := (between_neq hacd).2.2
  have hbd : b ≠ d := by
    intro hf; rw [hf] at habc; exact (noncol23 habc) (between_col hacd)
  obtain ⟨e, hbde⟩ := between_extend hbd
  have hbe := (between_neq hbde).2.1
  have hde := (between_neq hbde).2.2
  have hadb := col_noncol (between_col hacd) (noncol23 habc) had
  have hce : c ≠ e := by
    intro hf; rw [← hf] at hbde
    exact col_noncol (col12 (between_col hacd)) (noncol132 habc) hcd (col13 (between_col hbde))
  have hbea := col_noncol (between_col hbde) (noncol13 hadb) hbe
  have heda := col_noncol (col132 (between_col hbde)) (noncol12 hbea) hde.symm
  have hace := col_noncol (col23 (between_col hacd)) (noncol13 heda) hac
  have hdce := col_noncol (col132 (between_col hacd)) (noncol123 heda) hcd.symm
  have hebc := col_noncol (col13 (between_col hbde)) (noncol132 hdce) hbe.symm
  have hmeet : ((c-ₗe) ♥ (a-ₛd).inside) := ⟨c, pt_left_in_line c e, Or.inl hacd⟩
  rcases (pasch hadb (line_in_lines hce) (noncol_in23 hace) (noncol_in23 hdce)
      (noncol_in31 hebc) hmeet).1 with h | h
  · obtain ⟨x, hx⟩ := h
    rcases hx.2 with haxb | hf | hf
    · exact ⟨x, haxb⟩
    · rw [hf] at hx; exact absurd hx.1 (noncol_in23 hace)
    · rw [hf] at hx; exact absurd hx.1 (noncol_in31 hebc)
  · obtain ⟨x, hx⟩ := h
    have hxe : x = e := by
      refine two_line_one_pt (line_in_lines hce) (line_in_lines hbd.symm) ?_ hx.1
        ((seg_in_line d b) hx.2) (pt_right_in_line c e) (col_in21 (between_col hbde) hbd.symm)
      intro hf; apply noncol_in31 hebc; rw [hf]; exact pt_right_in_line d b
    rw [hxe] at hx
    rcases hx.2 with hf | hf | hf
    · exact absurd ⟨hf, (between_symm b d e).1 hbde⟩ between_contra.1
    · exact absurd hf.symm hde
    · exact absurd hf hbe.symm

end Hilbert