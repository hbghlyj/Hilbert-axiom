import RequestProject.Hilbert.Angle

/-!
# Congruence of segments, angles and triangles (Hilbert's axioms, Group III)

Lean 4 port of the congruence layer of T. Zhao's *Hilbert's axioms in Lean* development.
We extend the incidence–order–angle development with segment and angle congruence, making a
Hilbert plane, then develop congruence of triangles (SAS, supplementary angles, …).
-/

universe u

namespace Hilbert

open IncidenceGeometry IncidenceOrderGeometry

/-- A Hilbert plane extends incidence order geometry with two congruence relations on segments
and angles, subject to Hilbert's congruence axioms C1–C6. -/
class HilbertPlane extends IncidenceOrderGeometry where
  seg_congr : seg → seg → Prop
  C1 : ∀ {a b : Pt} {l : seg}, seg_proper l → a ≠ b → ∃ c : Pt, same_side_pt a b c ∧
    seg_congr l (a-ₛc) ∧ ∀ x : Pt, same_side_pt a b x → seg_congr l (a-ₛx) → x = c
  C2 : (∀ {s₁ s₂ s₃ : seg}, seg_congr s₁ s₂ → seg_congr s₁ s₃ → seg_congr s₂ s₃)
    ∧ ∀ s : seg, seg_congr s s
  C3 : ∀ {a b c d e f : Pt}, between a b c → between d e f
    → seg_congr (a-ₛb) (d-ₛe) → seg_congr (b-ₛc) (e-ₛf) → seg_congr (a-ₛc) (d-ₛf)
  ang_congr : ang → ang → Prop
  C4 : ∀ {α : ang} {a b p : Pt}, ang_proper α → a ≠ b → p ∉ (a-ₗb)
    → ∃ c : Pt, ang_congr α (∠[c, a, b]) ∧ same_side_line (a-ₗb) c p
    ∧ ∀ x : Pt, same_side_line (a-ₗb) c x → ang_congr α (∠[x, a, b]) → x ∈ (a-ᵣc).inside
  C5 : (∀ {α β γ : ang}, ang_congr α β → ang_congr α γ → ang_congr β γ)
    ∧ ∀ α : ang, ang_congr α α
  C6 : ∀ {a b c d e f : Pt}, noncol a b c → noncol d e f → seg_congr (a-ₛb) (d-ₛe)
    → seg_congr (a-ₛc) (d-ₛf) → ang_congr (∠[b, a, c]) (∠[e, d, f])
    → seg_congr (b-ₛc) (e-ₛf) ∧ ang_congr (∠[a, b, c]) (∠[d, e, f])
      ∧ ang_congr (∠[a, c, b]) (∠[d, f, e])

open HilbertPlane

variable [C : HilbertPlane]

notation:50 a " ≅ₛ " b => HilbertPlane.seg_congr a b

lemma extend_congr_seg {s : seg} {a b : Pts} (hs : seg_proper s) (hab : a ≠ b) :
    ∃ c : Pts, same_side_pt a b c ∧ (s ≅ₛ (a-ₛc))
      ∧ ∀ x : Pts, same_side_pt a b x → (s ≅ₛ (a-ₛx)) → x = c := C1 hs hab

lemma extend_congr_seg' {s : seg} {a b : Pts} (hs : seg_proper s) (hab : a ≠ b) :
    ∃ c : Pts, diff_side_pt a b c ∧ (s ≅ₛ (a-ₛc))
      ∧ ∀ x : Pts, diff_side_pt a b x → (s ≅ₛ (a-ₛx)) → x = c := by
        by_contra h_contra;
        -- By definition of $C$, we know that $C$ satisfies the axioms of a Hilbert plane.
        obtain ⟨C_axioms, C_plane⟩ := C;
        rename_i h1 h2 h3 h4 h5 h6;
        obtain ⟨c, hc⟩ := ‹IncidenceOrderGeometry›.B2 (show b ≠ a from Ne.symm hab);
        obtain ⟨d, hd⟩ := C_plane hs (by
        exact fun h => by have := between_neq hc; aesop; : a ≠ c);
        refine' h_contra ⟨ d, _, hd.2.1, _ ⟩;
        · exact Hilbert.diff_same_side_pt ( Hilbert.diff_side_pt_symm ( Hilbert.between_diff_side_pt.1 hc ) ) hd.1;
        · intro x hx hx';
          apply hd.2.2 x (diff_side_pt_cancel (by
          exact Hilbert.between_diff_side_pt.1 hc) hx) hx'

lemma seg_congr_refl (s : seg) : s ≅ₛ s := C2.2 s

lemma seg_congr_symm {s₁ s₂ : seg} : (s₁ ≅ₛ s₂) → (s₂ ≅ₛ s₁) :=
  fun h => C2.1 h (seg_congr_refl s₁)

lemma seg_congr_trans {s₁ s₂ s₃ : seg} : (s₁ ≅ₛ s₂) → (s₂ ≅ₛ s₃) → (s₁ ≅ₛ s₃) :=
  fun h₁ h₂ => C2.1 (seg_congr_symm h₁) h₂

lemma seg_unique_same_side {o a b : Pts} (hab : same_side_pt o a b) :
    ((o-ₛa) ≅ₛ (o-ₛb)) → a = b := by
      cases' eq_or_ne a o with ha ha <;> simp_all +decide;
      · grind +suggestions;
      · cases' C with C₁ C₂ C₃ C₄ C₅ C₆;
        cases' C₃ ( show seg_proper ( o-ₛa ) from by
                      exact seg_proper_iff_neq.2 ( Ne.symm ha ) ) ( show o ≠ a from by
                                                                exact Ne.symm ha ) with d hd;
        have := hd.2.2 a ( same_side_pt_refl ( by tauto ) ) ( by tauto );
        grind

lemma congr_seg_add {a b c d e f : Pts} : between a b c → between d e f
    → ((a-ₛb) ≅ₛ (d-ₛe)) → ((b-ₛc) ≅ₛ (e-ₛf)) → ((a-ₛc) ≅ₛ (d-ₛf)) :=
  fun h₁ h₂ h₃ h₄ => C3 h₁ h₂ h₃ h₄

lemma congr_seg_sub {a b c d e f : Pts} (habc : between a b c) (hdef : same_side_pt d e f)
    (habde : (a-ₛb) ≅ₛ (d-ₛe)) (hacdf : (a-ₛc) ≅ₛ (d-ₛf)) :
    between d e f ∧ ((b-ₛc) ≅ₛ (e-ₛf)) := by
      have hbc := (between_neq habc).2.2
      have hed := (same_side_pt_neq hdef).1
      obtain ⟨f', hdef', hbcef', -⟩ := extend_congr_seg' (seg_proper_iff_neq.2 hbc) hed
      rw [← between_diff_side_pt] at hdef'
      suffices hff : f = f' by
        rw [hff]; exact ⟨hdef', hbcef'⟩
      apply seg_unique_same_side
        (same_side_pt_trans (same_side_pt_symm hdef) (between_same_side_pt.1 hdef').1)
      apply seg_congr_trans (seg_congr_symm hacdf)
      exact congr_seg_add habc hdef' habde hbcef'

notation:50 a " ≅ₐ " b => HilbertPlane.ang_congr a b

lemma ang_congr_refl (α : ang) : α ≅ₐ α := C5.2 α

lemma ang_congr_symm {α β : ang} : (α ≅ₐ β) → (β ≅ₐ α) :=
  fun h => C5.1 h (ang_congr_refl α)

lemma ang_congr_trans {α β γ : ang} : (α ≅ₐ β) → (β ≅ₐ γ) → (α ≅ₐ γ) :=
  fun h₁ h₂ => C5.1 (ang_congr_symm h₁) h₂

lemma extend_congr_ang {α : ang} {a b p : Pts} :
    ang_proper α → a ≠ b → p ∉ (a-ₗb)
    → ∃ c : Pts, ang_congr α (∠[c, a, b]) ∧ same_side_line (a-ₗb) c p
      ∧ ∀ x : Pts, same_side_line (a-ₗb) c x → ang_congr α (∠[x, a, b]) → x ∈ (a-ᵣc).inside := C4

lemma extend_congr_ang' {α : ang} {a b p : Pts} :
    ang_proper α → a ≠ b → p ∉ (a-ₗb)
    → ∃ c : Pts, ang_congr α (∠[c, a, b]) ∧ diff_side_line (a-ₗb) c p := by
      revert ‹HilbertPlane›;
      intro C;
      obtain ⟨h1, h2, h3⟩ := C;
      rename_i h4 h5 h6;
      intro α a b p hα hab hp;
      obtain ⟨q, hq⟩ : ∃ q : Pts, between p a q := by
        exact Hilbert.between_extend ( show p ≠ a from fun h => hp <| h.symm ▸ Hilbert.pt_left_in_line a b );
      obtain ⟨c, hc⟩ : ∃ c : Pts, ‹ang → ang → Prop› α (∠[c, a, b]) ∧ same_side_line (line a b) c q ∧ ∀ x : Pts, same_side_line (line a b) c x → ‹ang → ang → Prop› α (∠[x, a, b]) → x ∈ (a-ᵣc).inside := by
        apply h4 hα hab;
        have := Hilbert.between_col hq;
        obtain ⟨ l, hl₁, hl₂, hl₃, hl₄ ⟩ := this;
        have := ‹IncidenceOrderGeometry›.I1 ( show a ≠ q from by
                                                rintro rfl;
                                                exact absurd hq ( by have := ‹IncidenceOrderGeometry›.B3.2 p a a; tauto ) );
        grind;
      have hkey := diff_side_pt_line (between_diff_side_pt.1 hq) (line_in_lines hab) (pt_left_in_line a b) hp (noncol_in13 (col_noncol (col12 (between_col hq)) (noncol_in13' hab hp) (by
      exact fun h => by subst h; exact absurd ( between_neq hq ) ( by tauto ) ;)));
      have := diff_same_side_line (line_in_lines hab) hkey (same_side_line_symm hc.2.1);
      exact ⟨ c, hc.1, diff_side_line_symm this ⟩

lemma ang_unique_same_side {o a b c : Pts} (hoa : o ≠ a) (hbc : same_side_line (o-ₗa) b c)
    (hoaboac : ∠[o, a, b] ≅ₐ ∠[o, a, c]) : same_side_pt a b c := by
      have hoab := (same_side_line_noncol hbc hoa).1
      rw [line_symm] at hbc
      obtain ⟨x, hoaboax, hxb, hu⟩ := extend_congr_ang (ang_proper_iff_noncol.2 hoab) hoa.symm
        (same_side_line_notin hbc).1
      rw [ang_symm x a o] at hoaboax
      rw [ang_symm] at hu
      rw [ang_symm, ang_symm o a c] at hoaboac
      have hb := hu b hxb (ang_congr_refl _)
      have hc := hu c (same_side_line_trans (line_in_lines hoa.symm) hxb hbc) hoaboac
      have hba := (noncol_neq hoab).2.2.symm
      have hca := (noncol_neq (same_side_line_noncol hbc hoa.symm).2).2.1.symm
      exact same_side_pt_trans (same_side_pt_symm (ray_in_neq hba hb)) (ray_in_neq hca hc)

/-- A triangle: three (ordered) vertices. -/
structure triang where
  v1 : Pts
  v2 : Pts
  v3 : Pts

/-- Two triangles are congruent if their corresponding sides and angles are congruent. -/
def tri_congr (t₁ t₂ : triang) : Prop :=
  ((t₁.v1-ₛt₁.v2) ≅ₛ (t₂.v1-ₛt₂.v2)) ∧ ((t₁.v1-ₛt₁.v3) ≅ₛ (t₂.v1-ₛt₂.v3))
    ∧ ((t₁.v2-ₛt₁.v3) ≅ₛ (t₂.v2-ₛt₂.v3))
    ∧ ((∠[t₁.v2, t₁.v1, t₁.v3] ≅ₐ ∠[t₂.v2, t₂.v1, t₂.v3])
      ∧ (∠[t₁.v1, t₁.v2, t₁.v3] ≅ₐ ∠[t₂.v1, t₂.v2, t₂.v3])
      ∧ (∠[t₁.v1, t₁.v3, t₁.v2] ≅ₐ ∠[t₂.v1, t₂.v3, t₂.v2]))

notation:50 a " ≅ₜ " b => tri_congr a b

lemma tri_congr_refl (t : triang) : t ≅ₜ t :=
  ⟨seg_congr_refl _, seg_congr_refl _, seg_congr_refl _,
    ang_congr_refl _, ang_congr_refl _, ang_congr_refl _⟩

lemma tri_congr_symm {t₁ t₂ : triang} : (t₁ ≅ₜ t₂) → (t₂ ≅ₜ t₁) :=
  fun h => ⟨seg_congr_symm h.1, seg_congr_symm h.2.1, seg_congr_symm h.2.2.1,
    ang_congr_symm h.2.2.2.1, ang_congr_symm h.2.2.2.2.1, ang_congr_symm h.2.2.2.2.2⟩

lemma tri_congr_trans {t₁ t₂ t₃ : triang} : (t₁ ≅ₜ t₂) → (t₂ ≅ₜ t₃) → (t₁ ≅ₜ t₃) :=
  fun h₁ h₂ => ⟨seg_congr_trans h₁.1 h₂.1, seg_congr_trans h₁.2.1 h₂.2.1,
    seg_congr_trans h₁.2.2.1 h₂.2.2.1, ang_congr_trans h₁.2.2.2.1 h₂.2.2.2.1,
    ang_congr_trans h₁.2.2.2.2.1 h₂.2.2.2.2.1, ang_congr_trans h₁.2.2.2.2.2 h₂.2.2.2.2.2⟩

/-- The triangle with the three given vertices. -/
def three_pt_triang (a b c : Pts) : triang := ⟨a, b, c⟩

notation:max "Δ" => three_pt_triang

lemma three_pt_triang_v1 (a b c : Pts) : (Δ a b c).v1 = a := rfl
lemma three_pt_triang_v2 (a b c : Pts) : (Δ a b c).v2 = b := rfl
lemma three_pt_triang_v3 (a b c : Pts) : (Δ a b c).v3 = c := rfl

lemma tri_congr12 {a b c a' b' c' : Pts} :
    ((Δ a b c) ≅ₜ (Δ a' b' c')) → ((Δ b a c) ≅ₜ (Δ b' a' c')) := by
      unfold tri_congr;
      grind +suggestions

lemma tri_congr13 {a b c a' b' c' : Pts} :
    ((Δ a b c) ≅ₜ (Δ a' b' c')) → ((Δ c b a) ≅ₜ (Δ c' b' a')) := by
      unfold tri_congr;
      unfold three_pt_triang at *;
      simp_all +decide [ seg_symm, ang_symm ]

lemma tri_congr23 {a b c a' b' c' : Pts} :
    ((Δ a b c) ≅ₜ (Δ a' b' c')) → ((Δ a c b) ≅ₜ (Δ a' c' b')) := by
      grind +suggestions

lemma tri_congr123 {a b c a' b' c' : Pts} :
    ((Δ a b c) ≅ₜ (Δ a' b' c')) → ((Δ b c a) ≅ₜ (Δ b' c' a')) :=
  fun h => tri_congr23 (tri_congr12 h)

lemma tri_congr132 {a b c a' b' c' : Pts} :
    ((Δ a b c) ≅ₜ (Δ a' b' c')) → ((Δ c a b) ≅ₜ (Δ c' a' b')) :=
  fun h => tri_congr23 (tri_congr13 h)

lemma tri_congr_seg {a b c a' b' c' : Pts} (h : (Δ a b c) ≅ₜ (Δ a' b' c')) :
    ((a-ₛb) ≅ₛ (a'-ₛb')) ∧ ((a-ₛc) ≅ₛ (a'-ₛc')) ∧ ((b-ₛc) ≅ₛ (b'-ₛc')) := by
      obtain ⟨h₁, h₂, h₃, h₄⟩ := h;
      exact ⟨ h₁, h₂, h₃ ⟩

lemma tri_congr_ang {a b c a' b' c' : Pts} (h : (Δ a b c) ≅ₜ (Δ a' b' c')) :
    (∠[a, b, c] ≅ₐ ∠[a', b', c']) ∧ (∠[b, a, c] ≅ₐ ∠[b', a', c'])
      ∧ (∠[a, c, b] ≅ₐ ∠[a', c', b']) := by
        obtain ⟨h₁, h₂, h₃, h₄⟩ := h;
        exact ⟨ h₄.2.1, h₄.1, h₄.2.2 ⟩

lemma SAS {ABC DEF : triang}
    (h₁ : noncol ABC.v1 ABC.v2 ABC.v3) (h₂ : noncol DEF.v1 DEF.v2 DEF.v3)
    (hs₁ : (ABC.v1-ₛABC.v2) ≅ₛ (DEF.v1-ₛDEF.v2)) (hs₂ : (ABC.v1-ₛABC.v3) ≅ₛ (DEF.v1-ₛDEF.v3))
    (ha : (∠[ABC.v2, ABC.v1, ABC.v3] ≅ₐ ∠[DEF.v2, DEF.v1, DEF.v3])) : ABC ≅ₜ DEF :=
  ⟨hs₁, hs₂, (C6 h₁ h₂ hs₁ hs₂ ha).1, ha, (C6 h₁ h₂ hs₁ hs₂ ha).2.1, (C6 h₁ h₂ hs₁ hs₂ ha).2.2⟩

lemma supplementary_congr {α α' β β' : ang}
    (h : supplementary α α') (h' : supplementary β β') : (α ≅ₐ β) → (α' ≅ₐ β') := by
      obtain ⟨a, b, c, d, hα, hα', hcad⟩ := h.1
      obtain ⟨a', b', c', d', hβ, hβ', hc'a'd'⟩ := h'.1
      intro hbacb'a'c'
      rw [hα, hα'] at h
      rw [hβ, hβ'] at h'
      rw [hα, hβ] at hbacb'a'c'
      rw [hα', hβ']
      have hac := (between_neq hcad).1.symm
      have hbac := ang_proper_iff_noncol.1 h.2.1
      have hbad := ang_proper_iff_noncol.1 h.2.2
      have hab := (noncol_neq hbac).1.symm
      have had := (noncol_neq hbad).2.2
      have hcd := (between_neq hcad).2.1
      have hb'a'c' := ang_proper_iff_noncol.1 h'.2.1
      have hb'a'd' := ang_proper_iff_noncol.1 h'.2.2
      have ha'b' := (noncol_neq hb'a'c').1.symm
      have ha'c' := (noncol_neq hb'a'c').2.2
      have ha'd' := (noncol_neq hb'a'd').2.2
      obtain ⟨c'', ha'c'', haca'c', -⟩ := extend_congr_seg (seg_proper_iff_neq.2 hac) ha'c'
      obtain ⟨b'', ha'b'', haba'b', -⟩ := extend_congr_seg (seg_proper_iff_neq.2 hab) ha'b'
      obtain ⟨d'', ha'd'', hada'd', -⟩ := extend_congr_seg (seg_proper_iff_neq.2 had) ha'd'
      rw [ang_eq_same_side_pt b' ha'c'', ang_symm b' a' c'', ang_eq_same_side_pt c'' ha'b'']
        at hbacb'a'c' h'
      rw [ang_eq_same_side_pt b' ha'd'', ang_symm b' a' d'', ang_eq_same_side_pt d'' ha'b''] at h'
      rw [ang_eq_same_side_pt b' ha'd'', ang_symm b' a' d'', ang_eq_same_side_pt d'' ha'b'']
      replace hc'a'd' : between c'' a' d'' := by
        rw [between_diff_side_pt]
        exact diff_same_side_pt (diff_same_side_pt (between_diff_side_pt.1 hc'a'd') ha'c'') ha'd''
      have hc'a'b' := ang_proper_iff_noncol.1 h'.2.1
      have hd'a'b' := ang_proper_iff_noncol.1 h'.2.2
      have hc'd' := (between_neq hc'a'd').2.1
      rw [ang_symm c'' a' b''] at hbacb'a'c'
      have h₁ : (Δ a b c) ≅ₜ (Δ a' b'' c'') :=
        SAS (noncol12 hbac) (noncol123 hc'a'b') haba'b' haca'c' hbacb'a'c'
      have h₂ : (Δ c b d) ≅ₜ (Δ c'' b'' d'') := by
        have n1 : noncol c b d := noncol23 (col_noncol (between_col hcad) (noncol13 hbac) hcd)
        have n2 : noncol c'' b'' d'' := noncol23 (col_noncol (between_col hc'a'd') hc'a'b' hc'd')
        have s1 : (c-ₛb) ≅ₛ (c''-ₛb'') := by
          rw [seg_symm, seg_symm c'' b'']; exact (tri_congr_seg h₁).2.2
        have s2 : (c-ₛd) ≅ₛ (c''-ₛd'') := by
          apply congr_seg_add hcad hc'a'd' _ hada'd'
          rw [seg_symm, seg_symm c'' a']; exact haca'c'
        have ang2 : ∠[b, c, d] ≅ₐ ∠[b'', c'', d''] := by
          rw [← ang_eq_same_side_pt b (between_same_side_pt.1 hcad).1,
            ← ang_eq_same_side_pt b'' (between_same_side_pt.1 hc'a'd').1, ang_symm,
            ang_symm b'' c'' a']
          exact (tri_congr_ang h₁).2.2
        exact SAS n1 n2 s1 s2 ang2
      have h₃ : (Δ d a b) ≅ₜ (Δ d'' a' b'') := by
        have n1 : noncol d a b := noncol13 hbad
        have n2 : noncol d'' a' b'' := hd'a'b'
        have s1 : (d-ₛa) ≅ₛ (d''-ₛa') := by
          rw [seg_symm, seg_symm d'' a']; exact hada'd'
        have s2 : (d-ₛb) ≅ₛ (d''-ₛb'') := by
          rw [seg_symm, seg_symm d'' b'']; exact (tri_congr_seg h₂).2.2
        have ang3 : ∠[a, d, b] ≅ₐ ∠[a', d'', b''] := by
          rw [ang_symm, ← ang_eq_same_side_pt b (between_same_side_pt.1 hcad).2, ang_symm,
            ang_symm a' d'' b'', ← ang_eq_same_side_pt b'' (between_same_side_pt.1 hc'a'd').2,
            ang_symm b'' d'' c'']
          exact (tri_congr_ang h₂).2.2
        exact SAS n1 n2 s1 s2 ang3
      rw [ang_symm]
      exact (tri_congr_ang h₃).1

lemma congr_ang_add {a b c d a' b' c' d' : Pts}
    (hd : inside_ang d (∠[b, a, c])) (hb'c' : diff_side_line (a'-ₗd') b' c') (ha'd' : a' ≠ d')
    (hbadb'a'd' : ∠[b, a, d] ≅ₐ ∠[b', a', d']) (hdacd'a'c' : ∠[d, a, c] ≅ₐ ∠[d', a', c']) :
    inside_ang d' (∠[b', a', c']) ∧ (∠[b, a, c] ≅ₐ ∠[b', a', c']) := by
      have hbac := inside_ang_proper hd
      rw [ang_proper_iff_noncol] at hbac
      have hab := (noncol_neq hbac).1.symm
      have hac := (noncol_neq hbac).2.2
      have ha'b' := (noncol_neq (diff_side_line_noncol hb'c' ha'd').1).2.1
      have ha'c' := (noncol_neq (diff_side_line_noncol hb'c' ha'd').2).2.1
      obtain ⟨e, he⟩ := crossbar hd
      have hda : e ≠ a := by
        intro hf; rw [hf] at he; exact noncol_in13 hbac ((seg_in_line b c) he.2)
      have hdb : e ≠ b := by
        intro hf; rw [hf] at he
        exact ((same_side_line_noncol (inside_three_pt_ang.1 hd).1) hab).2
          (col_in13' ((ray_in_line a d) he.1))
      have hdc : e ≠ c := by
        intro hf; rw [hf] at he
        exact ((same_side_line_noncol (inside_three_pt_ang.1 hd).2) hac).2
          (col_in13' ((ray_in_line a d) he.1))
      have hbdc := seg_in_neq hdb hdc he.2
      have hade := ray_in_neq hda he.1
      replace hd := ray_inside_ang hd hade
      rw [ang_eq_same_side_pt b hade] at hbadb'a'd'
      rw [ang_symm, ang_eq_same_side_pt c hade, ang_symm] at hdacd'a'c'
      rw [inside_three_pt_ang] at hd
      have habd := (same_side_line_noncol hd.1 hab).2
      have hacd := (same_side_line_noncol hd.2 hac).2
      have had := (noncol_neq habd).2.1
      obtain ⟨c'', ha'c'c'', haca'c', -⟩ := extend_congr_seg (seg_proper_iff_neq.2 hac) ha'c'
      obtain ⟨b'', ha'b'b'', haba'b', -⟩ := extend_congr_seg (seg_proper_iff_neq.2 hab) ha'b'
      obtain ⟨d'', ha'd'd'', hada'd', -⟩ := extend_congr_seg (seg_proper_iff_neq.2 had) ha'd'
      have ha'd'' := (same_side_pt_neq ha'd'd'').2.symm
      rw [two_pt_one_line (line_in_lines ha'd') (line_in_lines ha'd'') ha'd'
        (pt_left_in_line a' d') (pt_right_in_line a' d') (pt_left_in_line a' d'')
        (col_in13 ha'd'd''.2 ha'd'')] at hb'c'
      replace hb'c' := diff_side_line_symm (ray_diff_side_line ha'd'' hb'c' ha'b'b'')
      replace hb'c' := diff_side_line_symm (ray_diff_side_line ha'd'' hb'c' ha'c'c'')
      rw [ang_eq_same_side_pt b' ha'd'd'', ang_symm b' a' d'', ang_eq_same_side_pt d'' ha'b'b'',
        ang_symm d'' a' b''] at hbadb'a'd'
      rw [ang_eq_same_side_pt d' ha'c'c'', ang_symm d' a' c'', ang_eq_same_side_pt c'' ha'd'd'',
        ang_symm c'' a' d''] at hdacd'a'c'
      rw [ang_eq_same_side_pt b' ha'c'c'', ang_symm, ang_eq_same_side_pt c'' ha'b'b'', ang_symm]
      suffices hgoal : inside_ang d'' (∠[b'', a', c'']) ∧ (∠[b, a, c] ≅ₐ ∠[b'', a', c'']) from
        ⟨ray_inside_ang hgoal.1 (same_side_pt_symm ha'd'd''), hgoal.2⟩
      have ha'd'b' := (diff_side_line_noncol hb'c' ha'd'').1
      have ha'd'c' := (diff_side_line_noncol hb'c' ha'd'').2
      have h₁ : (Δ a b e) ≅ₜ (Δ a' b'' d'') :=
        SAS habd (noncol23 ha'd'b') haba'b' hada'd' hbadb'a'd'
      have h₂ : (Δ a e c) ≅ₜ (Δ a' d'' c'') :=
        SAS (noncol23 hacd) ha'd'c' hada'd' haca'c' hdacd'a'c'
      have hb'd' := (noncol_neq ha'd'b').2.2.symm
      obtain ⟨e', hb'd'e'⟩ := between_extend hb'd'
      have hb'e' := (between_neq hb'd'e').2.1
      have hd'e' := (between_neq hb'd'e').2.2
      have hb'e'a' := col_noncol (between_col hb'd'e') (noncol13 ha'd'b') hb'e'
      have hd'e'a' := col_noncol (col12 (between_col hb'd'e')) (noncol123 ha'd'b') hd'e'
      have hd'e'c' : same_side_pt d'' e' c'' := by
        apply ang_unique_same_side ha'd''
        · apply diff_side_line_cancel (line_in_lines ha'd'') _ hb'c'
          apply between_diff_side_line
          · exact noncol13 hb'e'a'
          · rw [between_symm]; exact hb'd'e'
        · apply ang_congr_trans _ (tri_congr_ang h₂).1
          apply supplementary_congr
          · rw [three_pt_ang_supplementary]
            exact ⟨hb'd'e', ha'd'b', noncol132 hd'e'a'⟩
          · rw [three_pt_ang_supplementary]
            exact ⟨hbdc, noncol23 habd, noncol23 hacd⟩
          · exact ang_congr_symm (tri_congr_ang h₁).2.2
      have hb'd'c' := between_same_side_pt' hb'd'e' hd'e'c'
      have hb'c'a' := col_noncol (between_col hb'd'c') (noncol13 ha'd'b') (between_neq hb'd'c').2.1
      refine ⟨hypo_inside_ang (noncol23 hb'c'a') hb'd'c', ?_⟩
      have hsT1 : (b-ₛa) ≅ₛ (b''-ₛa') := by rw [seg_symm, seg_symm b'' a']; exact haba'b'
      have hsT2 : (b-ₛc) ≅ₛ (b''-ₛc'') :=
        congr_seg_add hbdc hb'd'c' (tri_congr_seg h₁).2.2 (tri_congr_seg h₂).2.2
      have haT : ∠[a, b, c] ≅ₐ ∠[a', b'', c''] := by
        rw [← ang_eq_same_side_pt a (between_same_side_pt.1 hbdc).1,
          ← ang_eq_same_side_pt a' (between_same_side_pt.1 hb'd'c').1]
        exact (tri_congr_ang h₁).1
      have hT : (Δ b a c) ≅ₜ (Δ b'' a' c'') := SAS hbac (noncol23 hb'c'a') hsT1 hsT2 haT
      exact (tri_congr_ang hT).1

lemma congr_ang_sub {a b c d a' b' c' d' : Pts}
    (hd : inside_ang d (∠[b, a, c])) (h : same_side_line (a'-ₗb') d' c')
    (ha'b' : a' ≠ b') (h₁ : ∠[b, a, c] ≅ₐ ∠[b', a', c']) (h₂ : ∠[b, a, d] ≅ₐ ∠[b', a', d']) :
    inside_ang d' (∠[b', a', c']) ∧ (∠[d, a, c] ≅ₐ ∠[d', a', c']) := by
      have hbac := ang_proper_iff_noncol.1 (inside_ang_proper hd)
      have hac := (noncol_neq hbac).2.2
      rw [inside_three_pt_ang] at hd
      have hacd := (same_side_line_noncol hd.2 hac).2
      have ha'd' := (same_side_line_neq h).1.symm
      have ha'b'd' := (same_side_line_noncol h ha'b').1
      obtain ⟨c'', hdacd'a'c'', hc''b'⟩ := extend_congr_ang' (ang_proper_iff_noncol.2 (noncol132 hacd))
        ha'd' (noncol_in13 ha'b'd')
      rw [ang_symm c'' a' d'] at hdacd'a'c''
      have key := congr_ang_add (inside_three_pt_ang.2 hd) (diff_side_line_symm hc''b')
        ha'd' h₂ hdacd'a'c''
      have hc'c'' := same_side_line_trans (line_in_lines ha'b') (same_side_line_symm h)
        (same_side_line_symm (inside_three_pt_ang.1 key.1).1)
      rw [line_symm] at hc'c''
      have ha'c'c'' := ang_unique_same_side ha'b'.symm hc'c''
        (ang_congr_trans (ang_congr_symm h₁) key.2)
      rw [ang_eq_same_side_pt b' ha'c'c'', ang_eq_same_side_pt d' ha'c'c'']
      exact ⟨key.1, hdacd'a'c''⟩

/-- I.15 in Elements: vertical angles are congruent. -/
lemma vertical_ang_congr {a b a' b' o : Pts} (haob : noncol a o b) :
    between a o a' → between b o b' → (∠[a, o, b] ≅ₐ ∠[a', o, b']) := by
      intro haoa' hbob'
      have hoa' := (between_neq haoa').2.2
      have hob' := (between_neq hbob').2.2
      have hoa'b := col_noncol (col12 (between_col haoa')) (noncol12 haob) hoa'
      have hob'a' := col_noncol (col12 (between_col hbob')) (noncol23 hoa'b) hob'
      rw [between_symm] at haoa'
      apply supplementary_congr _ _ (ang_congr_refl (∠[b, o, a']))
      · rw [ang_symm a o b, three_pt_ang_supplementary]
        exact ⟨haoa', noncol132 hoa'b, noncol13 haob⟩
      · rw [ang_symm, three_pt_ang_supplementary]
        exact ⟨hbob', noncol12 hoa'b, noncol132 hob'a'⟩

end Hilbert