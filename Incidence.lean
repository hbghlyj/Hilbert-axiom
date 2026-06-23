import Mathlib

/-!
# Incidence geometry (Hilbert's axioms, Group I)

Lean 4 port of the incidence layer of T. Zhao's *Hilbert's axioms in Lean* development.
We model an incidence geometry as a class with a type of points `Pt` and a set of `lines`,
satisfying the three incidence axioms I1–I3.
-/

universe u

namespace Hilbert

/-- An incidence geometry: a type of points `Pt`, a set `lines` of subsets of `Pt`, and
the three incidence axioms.
* I1. Two distinct points lie on a unique line.
* I2. Every line contains at least two distinct points.
* I3. There exist three non-collinear points. -/
class IncidenceGeometry where
  Pt : Type u
  lines : Set (Set Pt)
  I1 : ∀ {a b : Pt}, a ≠ b → ∃ l ∈ lines,
    a ∈ l ∧ b ∈ l ∧ (∀ l' ∈ lines, a ∈ l' → b ∈ l' → l' = l)
  I2 : ∀ l ∈ lines, ∃ a b : Pt, a ≠ b ∧ a ∈ l ∧ b ∈ l
  I3 : ∃ a b c : Pt, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
    ¬(∃ l ∈ lines, a ∈ l ∧ b ∈ l ∧ c ∈ l)

/-- The type of points of the ambient incidence geometry. -/
abbrev Pts [I : IncidenceGeometry] : Type u := I.Pt
/-- The set of lines of the ambient incidence geometry. -/
abbrev Lines [I : IncidenceGeometry] : Set (Set (Pts)) := I.lines

variable [I : IncidenceGeometry]

open IncidenceGeometry

/-- The line through `a` and `b` (a singleton when `a = b`). -/
noncomputable def line (a b : Pts) :
    { L : Set Pts // (a ≠ b → L ∈ Lines) ∧ a ∈ L ∧ b ∈ L ∧ (a = b → L = {a}) } := by
  classical
  by_cases hab : a = b
  · exact ⟨{a}, fun h => absurd hab h, rfl, by rw [hab]; rfl, fun _ => rfl⟩
  · exact ⟨(I1 hab).choose, fun _ => (I1 hab).choose_spec.1,
      (I1 hab).choose_spec.2.1, (I1 hab).choose_spec.2.2.1, fun h => absurd h hab⟩

notation:100 a "-ₗ" b => (line a b : Set Pts)

/-- Two sets of points intersect when their intersection is nonempty. -/
def intersect (m n : Set Pts) : Prop := (m ∩ n).Nonempty

notation:90 m "♥" n => intersect m n

lemma intersect_symm {m n : Set Pts} : (m ♥ n) → (n ♥ m) := by
  unfold intersect; rw [Set.inter_comm]; exact id

/-- Two lines are parallel if they are disjoint lines. -/
def parallel (l₁ l₂ : Set Pts) : Prop := ¬(l₁ ♥ l₂) ∧ (l₁ ∈ Lines) ∧ (l₂ ∈ Lines)

notation:90 l₁ "∥ₗ" l₂ => parallel l₁ l₂

lemma parallel_symm {l₁ l₂ : Set Pts} : (l₁ ∥ₗ l₂) → (l₂ ∥ₗ l₁) := by
  rintro ⟨hl₁l₂, hl₁, hl₂⟩; exact ⟨fun hf => hl₁l₂ (intersect_symm hf), hl₂, hl₁⟩

lemma line_in_lines {a b : Pts} (hab : a ≠ b) : (a-ₗb) ∈ Lines := (line a b).2.1 hab

lemma pt_left_in_line (a b : Pts) : a ∈ (a-ₗb) := (line a b).2.2.1

lemma pt_right_in_line (a b : Pts) : b ∈ (a-ₗb) := (line a b).2.2.2.1

lemma one_pt_line (a : Pts) : ∃ l ∈ Lines, a ∈ l := by
  by_contra h;
  cases' h' : I.I3 with b hb;
  cases' hb with c hc; cases' hc with d hd; simp_all +decide ;
  obtain ⟨l₁, hl₁⟩ : ∃ l₁ ∈ I.lines, b ∈ l₁ ∧ a ∈ l₁ := by
    by_cases hab : b = a;
    · obtain ⟨l₂, hl₂⟩ : ∃ l₂ ∈ I.lines, a ∈ l₂ ∧ c ∈ l₂ := by
        exact I.I1 ( by aesop ) |> fun ⟨ l₂, hl₂ ⟩ => ⟨ l₂, hl₂.1, hl₂.2.1, hl₂.2.2.1 ⟩;
      grind;
    · exact Exists.imp ( by tauto ) ( I.I1 hab );
  exact h l₁ hl₁.1 hl₁.2.2

lemma two_pt_line_unique {a b : Pts} (hab : a ≠ b)
    {l : Set Pts} (hl : l ∈ Lines) (ha : a ∈ l) (hb : b ∈ l) : l = (a-ₗb) := by
      have := I.I1 hab;
      grind +splitImp

lemma two_pt_on_one_line {l : Set Pts} (hl : l ∈ Lines) :
    ∃ a b : Pts, a ≠ b ∧ a ∈ l ∧ b ∈ l := I2 l hl

lemma line_two_pt {a b : Pts} (hl : (a-ₗb) ∈ Lines) : a ≠ b := by
  obtain ⟨ c, d, hcd, hc, hd ⟩ := I.I2 _ hl;
  grind

lemma two_pt_one_line {l m : Set Pts} (hl : l ∈ Lines) (hm : m ∈ Lines)
    {a b : Pts} (hab : a ≠ b) (hal : a ∈ l) (hbl : b ∈ l) (ham : a ∈ m) (hbm : b ∈ m) :
    l = m :=
  (two_pt_line_unique hab hl hal hbl).trans (two_pt_line_unique hab hm ham hbm).symm

lemma line_symm (a b : Pts) : (a-ₗb) = (b-ₗa) := by
  grind +locals

lemma two_line_one_pt {l₁ l₂ : Set Pts} (hl₁ : l₁ ∈ Lines) (hl₂ : l₂ ∈ Lines) :
    ∀ {a b : Pts}, l₁ ≠ l₂ → a ∈ l₁ → a ∈ l₂ → b ∈ l₁ → b ∈ l₂ → a = b := by
      intro a b hne ha₁ ha₂ hb₁ hb₂; contrapose! hne; have := I.I1 ( show a ≠ b from by aesop ) ;
      grind

/-- Three points are collinear if they lie on a common line. -/
def col (a b c : Pts) : Prop := ∃ l ∈ Lines, a ∈ l ∧ b ∈ l ∧ c ∈ l

/-- Negation of collinearity. -/
def noncol (a b c : Pts) : Prop := ¬col a b c

lemma noncol_exist {a b : Pts} (hab : a ≠ b) : ∃ c : Pts, noncol a b c := by
  obtain ⟨ x, y, z, hxy, hxz, hyz, h ⟩ := I.I3;
  contrapose! h;
  simp_all +decide [ noncol ];
  obtain ⟨ l, hl₁, hl₂, hl₃ ⟩ := h x; obtain ⟨ m, hm₁, hm₂, hm₃ ⟩ := h y; obtain ⟨ n, hn₁, hn₂, hn₃ ⟩ := h z; use l; simp_all +decide [ col ] ;
  have := I.I1 hab; aesop;

lemma noncol_neq {a b c : Pts} (hf : noncol a b c) : a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  contrapose! hf; simp_all +decide [ noncol ];
  by_cases hab : a = b <;> by_cases hac : a = c <;> by_cases hbc : b = c <;> simp_all +decide [ col ];
  · obtain ⟨ l, hl ⟩ := I.I3;
    by_cases h : c = l;
    · obtain ⟨ m, hm ⟩ := I.I1 ( show l ≠ hl.choose from hl.choose_spec.choose_spec.1 ) ; use m; aesop;
    · exact ⟨ _, I.I1 ( show c ≠ l from h ) |> Classical.choose_spec |> And.left, I.I1 ( show c ≠ l from h ) |> Classical.choose_spec |> And.right |> And.left ⟩;
  · exact Exists.imp ( by tauto ) ( I.I1 hbc );
  · exact Exists.elim ( I.I1 hab ) fun l hl => ⟨ l, hl.1, hl.2.1, hl.2.2.1, hl.2.1 ⟩;
  · exact Exists.imp ( by tauto ) ( I.I1 hac )

lemma col12 {a b c : Pts} : col a b c → col b a c := by
  rintro ⟨l, hl, h⟩; exact ⟨l, hl, h.2.1, h.1, h.2.2⟩

lemma noncol12 {a b c : Pts} : noncol a b c → noncol b a c := by
  unfold noncol; exact fun h hc => h (col12 hc)

lemma col13 {a b c : Pts} : col a b c → col c b a := by
  rintro ⟨l, hl, h⟩; exact ⟨l, hl, h.2.2, h.2.1, h.1⟩

lemma noncol13 {a b c : Pts} : noncol a b c → noncol c b a := by
  unfold noncol; exact fun h hc => h (col13 hc)

lemma col23 {a b c : Pts} : col a b c → col a c b := by
  rintro ⟨l, hl, h⟩; exact ⟨l, hl, h.1, h.2.2, h.2.1⟩

lemma noncol23 {a b c : Pts} : noncol a b c → noncol a c b := by
  unfold noncol; exact fun h hc => h (col23 hc)

lemma col123 {a b c : Pts} : col a b c → col b c a := fun h => col23 (col12 h)

lemma col132 {a b c : Pts} : col a b c → col c a b := fun h => col23 (col13 h)

lemma noncol123 {a b c : Pts} : noncol a b c → noncol b c a := by
  unfold noncol; exact fun h hc => h (col132 hc)

lemma noncol132 {a b c : Pts} : noncol a b c → noncol c a b := by
  unfold noncol; exact fun h hc => h (col123 hc)

lemma col_trans {a b c d : Pts} (habc : col a b c) (habd : col a b d)
    (hab : a ≠ b) : col a c d := by
      -- By two_pt_one_line, we have l = m.
      have hl_eq_m : ∃ l ∈ I.lines, a ∈ l ∧ b ∈ l ∧ c ∈ l ∧ d ∈ l := by
        rcases habc with ⟨ l, hl, ha, hb, hc ⟩ ; rcases habd with ⟨ m, hm, ha', hb', hd ⟩; have := I.I1 hab; aesop;
      exact ⟨ hl_eq_m.choose, hl_eq_m.choose_spec.1, hl_eq_m.choose_spec.2.1, hl_eq_m.choose_spec.2.2.2.1, hl_eq_m.choose_spec.2.2.2.2 ⟩

lemma col_noncol {a b c d : Pts} (habc : col a b c) (habd : noncol a b d) :
    a ≠ c → noncol a c d :=
  fun hac hacd => habd (col_trans (col23 habc) hacd hac)

lemma col_in12 {a b c : Pts} : col a b c → a ≠ b → c ∈ (a-ₗb) := by
  grind +locals

lemma col_in21 {a b c : Pts} : col a b c → b ≠ a → c ∈ (b-ₗa) := by
  rw [line_symm]; exact fun habc hba => col_in12 habc hba.symm

lemma col_in13 {a b c : Pts} : col a b c → a ≠ c → b ∈ (a-ₗc) := by
  grind +locals

lemma col_in31 {a b c : Pts} : col a b c → c ≠ a → b ∈ (c-ₗa) := by
  rw [line_symm]; exact fun habc hca => col_in13 habc hca.symm

lemma col_in23 {a b c : Pts} : col a b c → b ≠ c → a ∈ (b-ₗc) := by
  grind +locals

lemma col_in32 {a b c : Pts} : col a b c → c ≠ b → a ∈ (c-ₗb) := by
  rw [line_symm]; exact fun habc hcb => col_in23 habc hcb.symm

lemma noncol_in12 {a b c : Pts} : noncol a b c → c ∉ (a-ₗb) :=
  fun habc hc => habc ⟨(a-ₗb), line_in_lines (noncol_neq habc).1,
    pt_left_in_line a b, pt_right_in_line a b, hc⟩

lemma noncol_in21 {a b c : Pts} : noncol a b c → c ∉ (b-ₗa) := by
  rw [line_symm]; exact noncol_in12

lemma noncol_in13 {a b c : Pts} : noncol a b c → b ∉ (a-ₗc) :=
  fun habc hb => habc ⟨(a-ₗc), line_in_lines (noncol_neq habc).2.1,
    pt_left_in_line a c, hb, pt_right_in_line a c⟩

lemma noncol_in31 {a b c : Pts} : noncol a b c → b ∉ (c-ₗa) := by
  rw [line_symm]; exact noncol_in13

lemma noncol_in23 {a b c : Pts} : noncol a b c → a ∉ (b-ₗc) :=
  fun habc ha => habc ⟨(b-ₗc), line_in_lines (noncol_neq habc).2.2, ha,
    pt_left_in_line b c, pt_right_in_line b c⟩

lemma noncol_in32 {a b c : Pts} : noncol a b c → a ∉ (c-ₗb) := by
  rw [line_symm]; exact noncol_in23

lemma col_in12' {a b c : Pts} : c ∈ (a-ₗb) → col a b c := by
  intro h; by_contra habc; exact (noncol_in12 habc) h

lemma col_in21' {a b c : Pts} : c ∈ (b-ₗa) → col a b c := by
  rw [line_symm]; exact col_in12'

lemma col_in13' {a b c : Pts} : b ∈ (a-ₗc) → col a b c := by
  intro h; by_contra habc; exact (noncol_in13 habc) h

lemma col_in31' {a b c : Pts} : b ∈ (c-ₗa) → col a b c := by
  rw [line_symm]; exact col_in13'

lemma col_in23' {a b c : Pts} : a ∈ (b-ₗc) → col a b c := by
  intro h; by_contra habc; exact (noncol_in23 habc) h

lemma col_in32' {a b c : Pts} : a ∈ (c-ₗb) → col a b c := by
  rw [line_symm]; exact col_in23'

lemma noncol_in12' {a b c : Pts} (hab : a ≠ b) : c ∉ (a-ₗb) → noncol a b c := by
  contrapose!; intro h; rw [noncol, not_not] at h; exact col_in12 h hab

lemma noncol_in21' {a b c : Pts} (hba : b ≠ a) : c ∉ (b-ₗa) → noncol a b c := by
  rw [line_symm]; exact noncol_in12' hba.symm

lemma noncol_in13' {a b c : Pts} (hac : a ≠ c) : b ∉ (a-ₗc) → noncol a b c := by
  contrapose!; intro h; rw [noncol, not_not] at h; exact col_in13 h hac

lemma noncol_in31' {a b c : Pts} (hca : c ≠ a) : b ∉ (c-ₗa) → noncol a b c := by
  rw [line_symm]; exact noncol_in13' hca.symm

lemma noncol_in23' {a b c : Pts} (hbc : b ≠ c) : a ∉ (b-ₗc) → noncol a b c := by
  contrapose!; intro h; rw [noncol, not_not] at h; exact col_in23 h hbc

lemma noncol_in32' {a b c : Pts} (hcb : c ≠ b) : a ∉ (c-ₗb) → noncol a b c := by
  rw [line_symm]; exact noncol_in23' hcb.symm

end Hilbert