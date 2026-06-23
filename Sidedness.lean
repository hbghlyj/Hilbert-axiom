import RequestProject.Hilbert.Segment

/-!
# Sidedness (Hilbert's axioms, Group II continued)

Lean 4 port of the sidedness layer: same/different side of a line, same/different side of a
point, and the betweenness transitivity theorems derived from Pasch.
-/

universe u

namespace Hilbert

open IncidenceGeometry IncidenceOrderGeometry

variable [B : IncidenceOrderGeometry]

/-- `a` and `b` are on the same side of line `l` when segment `ab` does not meet `l`. -/
def same_side_line (l : Set Pts) (a b : Pts) : Prop := ¬(l ♥ (a-ₛb).inside)

/-- `a` and `b` are on different sides of `l`: segment `ab` meets `l`, not at `a` or `b`. -/
def diff_side_line (l : Set Pts) (a b : Pts) : Prop :=
  (l ♥ (a-ₛb).inside) ∧ a ∉ l ∧ b ∉ l

lemma plane_separation {l : Set Pts} {a b : Pts} (ha : a ∉ l) (hb : b ∉ l) :
    (same_side_line l a b ∨ diff_side_line l a b)
      ∧ ¬(same_side_line l a b ∧ diff_side_line l a b) := by
        -- By definition of same_side_line and diff_side_line, exactly one of them holds.
        simp [same_side_line, diff_side_line] at *;
        tauto

lemma not_same_side_line {l : Set Pts} {a b : Pts} (ha : a ∉ l) (hb : b ∉ l) :
    ¬(same_side_line l a b) ↔ (diff_side_line l a b) := by
      have := @plane_separation B l a b ha hb; aesop;

lemma not_diff_side_line {l : Set Pts} {a b : Pts} (ha : a ∉ l) (hb : b ∉ l) :
    ¬(diff_side_line l a b) ↔ (same_side_line l a b) := by
      constructor <;> intro h <;> simp_all +decide [ diff_side_line, same_side_line ]

lemma same_side_line_refl {l : Set Pts} {a : Pts} (ha : a ∉ l) : same_side_line l a a := by
  unfold same_side_line;
  rw [ seg_singleton ];
  exact Set.not_nonempty_iff_eq_empty.mpr ( by aesop )

lemma same_side_line_symm {l : Set Pts} {a b : Pts} :
    same_side_line l a b → same_side_line l b a := by
      simp +decide [ same_side_line ];
      grind +suggestions

lemma diff_side_line_symm {l : Set Pts} {a b : Pts} :
    diff_side_line l a b → diff_side_line l b a := by
      intro h
      unfold diff_side_line at h ⊢
      simp_all +decide [ Hilbert.seg_symm ]

lemma same_side_line_notin {x y : Pts} {l : Set Pts} :
    same_side_line l x y → x ∉ l ∧ y ∉ l := by
      contrapose!;
      intro hxy; by_cases hx : x ∈ l <;> simp_all +decide [ same_side_line ] ;
      · exact ⟨ x, hx, pt_left_in_seg x y ⟩;
      · exact ⟨ y, hxy, by exact pt_right_in_seg x y ⟩

lemma same_side_line_neq {a b x y : Pts} :
    same_side_line (a-ₗb) x y → x ≠ a ∧ x ≠ b := by
      grind +suggestions

lemma same_side_line_neq' {a b x y : Pts} :
    same_side_line (a-ₗb) x y → y ≠ a ∧ y ≠ b :=
  fun hxy => same_side_line_neq (same_side_line_symm hxy)

lemma same_side_line_noncol {a b c d : Pts} :
    same_side_line (a-ₗb) c d → a ≠ b → noncol a b c ∧ noncol a b d := by
      intro hcd hab;
      constructor;
      · intro h;
        exact absurd ( same_side_line_notin hcd ) ( by rintro ⟨ hc, hd ⟩ ; exact hc <| col_in12 h hab );
      · intro h;
        -- Since $a$, $b$, and $d$ are collinear, $d$ lies on the line $a-ₗb$.
        have hd : d ∈ (a-ₗb) := by
          convert col_in12 h hab using 1;
        exact absurd ( same_side_line_notin hcd ) ( by aesop )

lemma diff_side_line_neq {a b x y : Pts} :
    diff_side_line (a-ₗb) x y → x ≠ a ∧ x ≠ b := by
      intro hxy;
      constructor <;> intro h <;> have := hxy.2.1 <;> have := hxy.2.2 <;> simp_all +decide [ pt_left_in_line, pt_right_in_line ]

lemma diff_side_line_neq' {a b x y : Pts} :
    diff_side_line (a-ₗb) x y → y ≠ a ∧ y ≠ b :=
  fun hxy => diff_side_line_neq (diff_side_line_symm hxy)

lemma diff_side_line_neq'' {a b : Pts} {l : Set Pts}
    (hlab : diff_side_line l a b) : a ≠ b := by
      intro hab;
      simp [hab, diff_side_line] at hlab;
      obtain ⟨ x, hx ⟩ := hlab.1;
      simp_all +decide [ seg_singleton ]

lemma diff_side_line_noncol {a b c d : Pts} :
    diff_side_line (a-ₗb) c d → a ≠ b → noncol a b c ∧ noncol a b d :=
  fun hcd hab => ⟨noncol_in12' hab hcd.2.1, noncol_in12' hab hcd.2.2⟩

lemma same_side_line_trans_noncol {l : Set Pts} (hl : l ∈ Lines) {a b c : Pts} :
    noncol a b c → same_side_line l a b → same_side_line l b c → same_side_line l a c := by
      intro h1 h2 h3 h4
      have h5 : same_side_line l a b ∧ same_side_line l c b := by
        exact ⟨ h2, same_side_line_symm h3 ⟩;
      have := pasch ( show noncol a c b from ?_ ) hl ?_ ?_ ?_ ?_ <;> simp_all +decide [ noncol, noncol12, noncol13, noncol23 ];
      · simp_all +decide [ same_side_line, Set.Nonempty ];
      · convert h1 using 1;
        constructor <;> rintro ⟨ l, hl, ha, hb, hc ⟩ <;> use l, hl;
      · grind +suggestions;
      · exact fun h => h5.2 |> fun h' => h' |> fun h'' => by have := same_side_line_notin h''; tauto;
      · exact fun h => h5.2 |> fun h' => h' |> fun h'' => by have := same_side_line_notin h''; tauto;

lemma same_side_line_trans {l : Set Pts} (hl : l ∈ Lines) {a b c : Pts} :
    same_side_line l a b → same_side_line l b c → same_side_line l a c := by
  by_cases hcol : col a b c
  · intro hlab hlbc
    by_cases hab : a = b
    · rw [← hab] at hlbc; exact hlbc
    by_cases hbc : b = c
    · rw [hbc] at hlab; exact hlab
    by_cases hac : a = c
    · rw [hac]; exact same_side_line_refl (same_side_line_notin hlbc).2
    obtain ⟨m, hm, ham, hbm, hcm⟩ := hcol
    have hd : ∃ d : Pts, d ∈ l ∧ d ∉ m := by
      obtain ⟨x, y, hxy, hxl, hyl⟩ := two_pt_on_one_line hl
      have hlm : l ≠ m := by
        intro hlm; rw [← hlm] at ham; exact (same_side_line_notin hlab).1 ham
      by_contra hcon; push_neg at hcon
      exact hxy (two_line_one_pt hl hm hlm hxl (hcon x hxl) hyl (hcon y hyl))
    obtain ⟨d, hdl, hdm⟩ := hd
    have habd : noncol a b d := by
      apply noncol_in12' hab
      rw [two_pt_one_line (line_in_lines hab) hm hab (pt_left_in_line a b)
        (pt_right_in_line a b) ham hbm]
      exact hdm
    have had := (noncol_neq habd).2.1
    obtain ⟨e, hdae⟩ := between_extend had.symm
    have hae := (between_neq hdae).2.2
    have hlae : same_side_line l a e := by
      intro hmeet
      obtain ⟨f, hf⟩ := hmeet
      have hflae : f ∈ l ∧ f ∈ (a-ₗe) := ⟨hf.1, seg_in_line a e hf.2⟩
      have hdlae : d ∈ l ∧ d ∈ (a-ₗe) := ⟨hdl, col_in23 (between_col hdae) hae⟩
      have hneq : l ≠ (a-ₗe) := by
        intro hfeq; have h1 := (same_side_line_notin hlab).1; rw [hfeq] at h1
        exact h1 (pt_left_in_line a e)
      have hdf := two_line_one_pt hl (line_in_lines (between_neq hdae).2.2) hneq
        hdlae.1 hdlae.2 hflae.1 hflae.2
      rw [hdf] at hdae
      have hbn := between_neq hdae
      rcases hf.2 with hff | hff | hff
      · exact between_contra.1 ⟨hff, hdae⟩
      · exact hbn.1 hff
      · exact hbn.2.1 hff
    have hbae := noncol132 (col_noncol (col12 (between_col hdae)) (noncol23 habd) hae)
    have hebc := noncol132 (col_noncol ⟨m, hm, hbm, ham, hcm⟩ hbae hbc)
    have haec := noncol23 (col_noncol ⟨m, hm, ham, hbm, hcm⟩ (noncol12 hbae) hac)
    have hlbe := same_side_line_trans_noncol hl hbae (same_side_line_symm hlab) hlae
    have hlec := same_side_line_trans_noncol hl hebc (same_side_line_symm hlbe) hlbc
    exact same_side_line_trans_noncol hl haec hlae hlec
  · intro hlab hlbc
    exact same_side_line_trans_noncol hl hcol hlab hlbc

/-- `a` and `b` are on the same side of point `o`: collinear and `o` is not in segment `ab`. -/
def same_side_pt (o a b : Pts) : Prop := o ∉ (a-ₛb).inside ∧ col o a b

/-- `a` and `b` are on different sides of `o`: `o ∈ ab` and `o` is neither endpoint. -/
def diff_side_pt (o a b : Pts) : Prop := o ∈ (a-ₛb).inside ∧ a ≠ o ∧ b ≠ o

lemma same_side_pt_neq {o a b : Pts} (hoab : same_side_pt o a b) : a ≠ o ∧ b ≠ o := by
  constructor <;> rintro rfl;
  · exact hoab.1 ( by exact Hilbert.pt_left_in_seg _ _ );
  · exact hoab.1 ( by exact Hilbert.pt_right_in_seg _ _ )

lemma diff_side_pt_col {o a b : Pts} : diff_side_pt o a b → col o a b := by
  intro h;
  obtain ⟨h₁, h₂⟩ := h;
  by_cases hab : a = b <;> simp_all +decide [ col ];
  · obtain ⟨ l, hl ⟩ := B.I1 ( show o ≠ b from by tauto ) ; use l; aesop;
  · exact ⟨ _, line_in_lines hab, seg_in_line a b h₁, pt_left_in_line a b, pt_right_in_line a b ⟩

theorem line_separation {p a b : Pts} (hpab : col p a b) (hap : a ≠ p) (hbp : b ≠ p) :
    (same_side_pt p a b ∨ diff_side_pt p a b)
      ∧ ¬(same_side_pt p a b ∧ diff_side_pt p a b) := by
        simp_all +decide [ same_side_pt, diff_side_pt ];
        exact em' _

lemma not_same_side_pt {p a b : Pts} (hpab : col p a b) (ha : a ≠ p) (hb : b ≠ p) :
    (¬same_side_pt p a b ↔ diff_side_pt p a b) := by
      unfold same_side_pt diff_side_pt;
      grind

lemma not_diff_side_pt {p a b : Pts} (hpab : col p a b) (ha : a ≠ p) (hb : b ≠ p) :
    (¬diff_side_pt p a b ↔ same_side_pt p a b) := by
      grind +suggestions

lemma same_side_pt_refl {a b : Pts} (hab : a ≠ b) : same_side_pt a b b := by
  constructor;
  · simp +decide [ *, Hilbert.seg_singleton ];
  · obtain ⟨ l, hl ⟩ := B.I1 hab;
    exact ⟨ l, hl.1, hl.2.1, hl.2.2.1, hl.2.2.1 ⟩

lemma same_side_pt_symm {a b c : Pts} : same_side_pt a b c → same_side_pt a c b := by
  intro h;
  refine' ⟨ _, _ ⟩;
  · rw [ seg_symm ] ; exact h.1;
  · exact col23 h.2

lemma diff_side_pt_symm {a b c : Pts} : diff_side_pt a b c → diff_side_pt a c b := by
  intro h
  unfold diff_side_pt at h ⊢
  simp_all +decide [ Hilbert.seg_symm ]

lemma same_side_pt_line {a b c : Pts} (habc : same_side_pt a b c) {l : Set Pts}
    (hl : l ∈ Lines) (hal : a ∈ l) (hbl : b ∉ l) (hcl : c ∉ l) : same_side_line l b c := by
      by_cases hbc : b = c;
      · simp_all +decide [ same_side_line ];
        simp_all +decide [ Set.Nonempty, seg_singleton ];
        unfold intersect; aesop;
      · -- Suppose l meets (b-ₛc).inside at x. Since a ∈ l, b,c ∉ l, l ≠ (b-ₗc).
        by_contra h_contra
        obtain ⟨x, hx⟩ : ∃ x, x ∈ l ∧ x ∈ (b-ₛc).inside := by
          unfold same_side_line at h_contra; aesop;
        -- Since $a \in l$, $b, c \notin l$, and $x \in l$, $l \neq (b-ₗc)$. The point $a$ is on $l$ and on $(b-ₗc)$ (col_in23 of habc.2), and $x$ is on $l$ and on $(b-ₗc)$ (seg_in_line); by two_line_one_pt $a = x$, so $a \in (b-ₛc).inside$, contradicting habc.1 (a ∉ (b-ₛc).inside).
        have h_eq : a = x := by
          apply two_line_one_pt hl (line_in_lines hbc);
          · grind +splitImp;
          · assumption;
          · exact col_in23 habc.2 ( by tauto );
          · tauto;
          · exact seg_in_line _ _ hx.2;
        exact habc.1 ( h_eq ▸ hx.2 )

lemma between_diff_side_pt {a b c : Pts} : between a b c ↔ diff_side_pt b a c := by
  unfold diff_side_pt;
  simp [Hilbert.two_pt_seg];
  grind +suggestions

lemma diff_side_pt_neq' {a b c : Pts} (habc : diff_side_pt a b c) : b ≠ c := by
  obtain ⟨hac, hbc⟩ := habc;
  cases' hac with hac hac;
  · have := B.B1 hac; aesop;
  · grind

lemma diff_side_pt_line {a b c : Pts} (habc : diff_side_pt a b c) {l : Set Pts}
    (hl : l ∈ Lines) (hal : a ∈ l) (hbl : b ∉ l) (hcl : c ∉ l) : diff_side_line l b c :=
  ⟨⟨a, hal, by left; exact between_diff_side_pt.2 habc⟩, hbl, hcl⟩

lemma between_same_side_pt_prep {a b c : Pts} : between a b c → same_side_pt a b c := by
  grind +suggestions

lemma between_same_side_pt {a b c : Pts} :
    between a b c ↔ same_side_pt a b c ∧ same_side_pt c a b := by
      constructor;
      · grind +suggestions;
      · intro h
        obtain ⟨h_same_side_a, h_same_side_c⟩ := h;
        -- By definition of `same_side_pt`, we know that `a`, `b`, and `c` are distinct and collinear.
        have h_distinct : a ≠ b ∧ a ≠ c ∧ b ≠ c := by
          unfold same_side_pt at h_same_side_a h_same_side_c;
          unfold two_pt_seg at *; aesop;
        have h_collinear : col a b c := by
          exact h_same_side_a.2;
        grind +suggestions

lemma same_side_line_pt {a b c : Pts} (habc : col a b c) (l : Set Pts)
    (hl : l ∈ Lines) (hal : a ∈ l) (hbl : b ∉ l) (hcl : c ∉ l) (hlbc : same_side_line l b c) :
    same_side_pt a b c := by
      contrapose! hlbc;
      unfold same_side_pt at hlbc; simp_all +decide [ same_side_line ] ;
      exact ⟨ a, hal, hlbc ⟩

lemma diff_side_line_pt {a b c : Pts} (habc : col a b c) (l : Set Pts)
    (hl : l ∈ Lines) (hal : a ∈ l) (hbl : b ∉ l) (hcl : c ∉ l) (hlbc : diff_side_line l b c) :
    diff_side_pt a b c := by
      contrapose! hlbc; have := plane_separation hbl hcl; simp_all +decide [ diff_side_line ] ;
      have := same_side_pt_line ( show same_side_pt a b c from by
                                    exact ⟨ fun h => hlbc ⟨ h, by aesop ⟩, habc ⟩ ) hl hal hbl hcl; simp_all +decide [ diff_side_line ] ;

lemma line_pt_exist {a b c : Pts} (habc : col a b c) (hab : a ≠ b) (hac : a ≠ c) :
    ∃ l ∈ Lines, a ∈ l ∧ b ∉ l ∧ c ∉ l := by
      obtain ⟨c, hc⟩ : ∃ c : Pts, noncol a b c := by
        apply noncol_exist hab;
      use (a-ₗc);
      grind +suggestions

lemma same_side_pt_trans {a b c d : Pts} :
    same_side_pt a b c → same_side_pt a c d → same_side_pt a b d := by
      intros hbc hcd;
      obtain ⟨l, hl, hla, hlb, hlc⟩ : ∃ l ∈ Lines, a ∈ l ∧ b ∉ l ∧ c ∉ l := by
        apply line_pt_exist;
        · exact hbc.2;
        · exact fun h => by have := same_side_pt_neq hbc; aesop;
        · exact fun h => by have := same_side_pt_neq hbc; aesop;
      have hld : d ∉ l := by
        have hlc' : col a c d := by
          exact hcd.2;
        grind +suggestions;
      apply same_side_line_pt;
      any_goals assumption;
      · have hcol : col a b c ∧ col a c d := by
          exact ⟨ hbc.2, hcd.2 ⟩;
        grind +suggestions;
      · grind +suggestions

lemma between_same_side_pt' {a b c d : Pts} (habc : between a b c)
    (hbcd : same_side_pt b c d) : between a b d := by
      have hbc : col a b c := by
        exact B.B1 habc |>.2.2.2.2;
      have hbd : col a b d := by
        have hbd : col a b c ∧ col b c d := by
          exact ⟨ hbc, hbcd.2 ⟩;
        grind +suggestions;
      by_contra h_contra;
      have h_contra' : same_side_pt b a d := by
        grind +suggestions;
      have h_contra'' : same_side_pt b a c := by
        apply same_side_pt_trans h_contra' (same_side_pt_symm hbcd);
      grind +suggestions

lemma between_trans {a b c d : Pts} :
    between a b c → between b c d → between a b d ∧ between a c d := by
      convert B.B3.2 a b d using 1; all_goals grind +suggestions

lemma between_trans' {a b c d : Pts} :
    between a b d → between b c d → between a b c ∧ between a c d := by
      grind +suggestions

lemma same_side_pt_between {a b c : Pts} :
    same_side_pt a b c → b ≠ c → between a b c ∨ between a c b := by
      intro habc hbc;
      have := @B.B3;
      obtain ⟨l, hl⟩ : ∃ l ∈ Lines, a ∈ l ∧ b ∈ l ∧ c ∈ l := by
        exact habc.2;
      grind +suggestions

lemma between_same_side_pt_between {a b c d : Pts} :
    between a b c → same_side_pt b c d → between a b d := by
      grind +suggestions

lemma diff_side_pt_cancel {a b c d : Pts} :
    diff_side_pt a b c → diff_side_pt a b d → same_side_pt a c d := by
      intro hbc hbd
      by_cases hcd : c = d;
      · simp_all +decide [ same_side_pt, diff_side_pt ];
        simp_all +decide [ Hilbert.seg_singleton, Hilbert.col ];
        exact ⟨ by tauto, by have := B.I1 ( show a ≠ d from by tauto ) ; tauto ⟩;
      · by_contra h_contra;
        have hbc' : between b a c := by
          apply (between_diff_side_pt).mpr hbc
        have hbd' : between b a d := by
          grind +suggestions
        have hcd' : between c a d := by
          grind +suggestions;
        have := B.B3.2 b c d; simp_all +decide [ between_symm ] ;
        grind +suggestions

lemma diff_side_line_cancel {l : Set Pts} (hl : l ∈ Lines) {a b c : Pts} :
    diff_side_line l a b → diff_side_line l b c → same_side_line l a c := by
      intro h1 h2
      by_cases hcol : col a b c;
      · obtain ⟨x, hx⟩ : ∃ x : Pts, x ∈ l ∧ x ∈ (a-ₛb).inside ∧ x ≠ a ∧ x ≠ b := by
          obtain ⟨ x, hx ⟩ := h1.1;
          exact ⟨ x, hx.1, hx.2, by rintro rfl; exact h1.2.1 hx.1, by rintro rfl; exact h1.2.2 hx.1 ⟩
        obtain ⟨y, hy⟩ : ∃ y : Pts, y ∈ l ∧ y ∈ (b-ₛc).inside ∧ y ≠ b ∧ y ≠ c := by
          obtain ⟨ y, hy ⟩ := h2.1;
          exact ⟨ y, hy.1, hy.2, by rintro rfl; exact h2.2.1 hy.1, by rintro rfl; exact h2.2.2 hy.1 ⟩;
        -- Show x = y (two_line_one_pt on l and (a-ₗb), with y on (a-ₗb) via collinearity).
        have hxy : x = y := by
          have hxy : x ∈ (a-ₗb) ∧ y ∈ (a-ₗb) := by
            have hx_in_line : x ∈ (a-ₗb) := by
              exact Hilbert.seg_in_line _ _ hx.2.1
            have hy_in_line : y ∈ (b-ₗc) := by
              exact seg_in_line _ _ hy.2.1;
            have hy_in_line : y ∈ (a-ₗb) := by
              have h_collinear : col a b c := hcol
              have h_distinct : a ≠ b ∧ b ≠ c := by
                grind
              grind +suggestions;
            exact ⟨ hx_in_line, hy_in_line ⟩;
          grind +suggestions;
        -- Apply same_side_pt_line to diff_side_pt_cancel of (between_diff_side_pt of a-x-b reversed) and (between_diff_side_pt of b-y-c).
        have h_same_side : same_side_pt x a c := by
          apply diff_side_pt_cancel;
          any_goals exact b;
          · unfold diff_side_pt; simp_all +decide [ same_side_pt ] ;
            exact ⟨ by rw [ seg_symm ] ; exact hx.1, by tauto, by tauto ⟩;
          · unfold diff_side_pt; aesop;
        apply same_side_pt_line;
        exact h_same_side;
        · assumption;
        · grind;
        · exact h1.2.1;
        · exact h2.2.2;
      · by_contra h_contra;
        obtain ⟨h3, h4⟩ : diff_side_line l a c ∧ diff_side_line l b c := by
          exact ⟨ not_same_side_line ( h1.2.1 ) ( h2.2.2 ) |>.1 h_contra, h2 ⟩;
        have := pasch hcol hl ( h1.2.1 ) ( h1.2.2 ) ( h3.2.2 ) ; simp_all +decide [ diff_side_line ] ;

lemma diff_same_side_line {l : Set Pts} (hl : l ∈ Lines) {a b c : Pts} :
    diff_side_line l a b → same_side_line l b c → diff_side_line l a c := by
      grind +suggestions

lemma same_diff_side_line {l : Set Pts} (hl : l ∈ Lines) {a b c : Pts} :
    same_side_line l a b → diff_side_line l b c → diff_side_line l a c :=
  fun hlab hlbc =>
    diff_side_line_symm (diff_same_side_line hl (diff_side_line_symm hlbc)
      (same_side_line_symm hlab))

lemma diff_same_side_pt {a b c d : Pts} :
    diff_side_pt a b c → same_side_pt a b d → diff_side_pt a c d := by
      intro hcd hbd;
      simp_all +decide [ same_side_pt, diff_side_pt ];
      cases hcd.1 <;> simp_all +decide [ Hilbert.two_pt_seg ];
      grind +suggestions

lemma two_pt_seg_pt_prep {a b a' b' : Pts} :
    (a-ₛb) = (a'-ₛb') → a = a' → b = b' := by
      simp_all +decide [ two_pt_seg ];
      simp_all +decide [ Set.Subset.antisymm_iff, Set.subset_def ];
      grind +suggestions

lemma two_pt_seg_pt {a b a' b' : Pts} :
    (a-ₛb) = (a'-ₛb') → (a = a' ∧ b = b') ∨ (a = b' ∧ b = a') := by
      by_cases h : a = a' <;> by_cases h' : a = b' <;> simp +decide [ h, h', Hilbert.two_pt_seg ];
      · cases eq_or_ne b b' <;> simp_all +decide [ Set.ext_iff ];
        use b; simp_all +decide [ Hilbert.between_symm ] ;
        exact fun h => by have := B.B1 h; tauto;
      · intro h_eq; have := h_eq; simp_all +decide [ Set.Subset.antisymm_iff, Set.subset_def ] ;
        grind +suggestions;
      · intro h_eq; have := h_eq.symm; simp_all +decide [ Set.Subset.antisymm_iff, Set.subset_def ] ;
        grind +suggestions;
      · simp_all +decide [ Set.Subset.antisymm_iff, Set.subset_def ];
        grind +suggestions

end Hilbert