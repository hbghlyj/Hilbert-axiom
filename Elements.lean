import RequestProject.Hilbert.SegLt
import RequestProject.Hilbert.AngLt

/-!
# Euclid's Elements (selected propositions, Hilbert's axioms)

Lean 4 port of the propositions of Euclid's Book I needed for the angle–side inequality
("the greater side lies opposite the greater angle", **I.18**), built synthetically from
Hilbert's axioms (valid in both Euclidean and hyperbolic neutral geometry).

The chain is: isosceles base angles (I.5/I.6), SSS (I.8), existence of isosceles triangles,
angle bisectors (I.9), midpoints (I.10), the exterior-angle inequality (I.16), and finally
the angle–side inequality (I.18).
-/

universe u

namespace Hilbert

open IncidenceGeometry IncidenceOrderGeometry HilbertPlane

variable [C : HilbertPlane]

/-- I.5 in Elements: the base angles of an isosceles triangle are congruent. -/
theorem isosceles {a b c : Pts} (habc : noncol a b c) :
    ((a-ₛb) ≅ₛ (a-ₛc)) → ((∠[a, b, c]) ≅ₐ (∠[a, c, b])) := by
      intro habac
      have hab := (noncol_neq habc).1
      have hac := (noncol_neq habc).2.1
      obtain ⟨d, habd⟩ := between_extend hab
      obtain ⟨x, hacx⟩ := between_extend hac
      have hbd := (between_neq habd).2.2
      obtain ⟨e, hcxe, hbdce, -⟩ :=
        extend_congr_seg (seg_proper_iff_neq.2 hbd) (between_neq hacx).2.2
      have hace := between_same_side_pt_between hacx hcxe
      have had := (between_neq habd).2.1
      have hae := (between_neq hace).2.1
      have hadc := col_noncol (between_col habd) habc had
      have haeb := col_noncol (between_col hace) (noncol23 habc) hae
      have hadcaeb : ((Δ a d c) ≅ₜ (Δ a e b)) := by
        have hs1 : (a-ₛd) ≅ₛ (a-ₛe) := congr_seg_add habd hace habac hbdce
        have hs2 : (a-ₛc) ≅ₛ (a-ₛb) := seg_congr_symm habac
        have ha2 : ∠[d, a, c] ≅ₐ ∠[e, a, b] := by
          rw [ang_symm, ← ang_eq_same_side_pt c (between_same_side_pt.1 habd).1]
          rw [ang_symm, ang_symm e a b]
          rw [ang_eq_same_side_pt b (between_same_side_pt.1 hace).1]
          exact ang_congr_refl _
        exact SAS hadc haeb hs1 hs2 ha2
      have hce := (between_neq hace).2.2
      have hdbc := col_noncol (col132 (between_col habd)) (noncol12 hadc) hbd.symm
      have hecb := col_noncol (col132 (between_col hace)) (noncol12 haeb) hce.symm
      have hdbcecb : ((Δ d b c) ≅ₜ (Δ e c b)) := by
        have hs1 : (d-ₛb) ≅ₛ (e-ₛc) := by rw [seg_symm, seg_symm e c]; exact hbdce
        have hs2 : (d-ₛc) ≅ₛ (e-ₛb) := (tri_congr_seg hadcaeb).2.2
        have ha2 : ∠[b, d, c] ≅ₐ ∠[c, e, b] := by
          rw [ang_symm, ← ang_eq_same_side_pt c (between_same_side_pt.1 habd).2]
          rw [ang_symm c e b, ← ang_eq_same_side_pt b (between_same_side_pt.1 hace).2]
          rw [ang_symm, ang_symm b e a]
          exact (tri_congr_ang hadcaeb).1
        exact SAS hdbc hecb hs1 hs2 ha2
      have hkey := (tri_congr_ang hdbcecb).1
      rw [ang_symm, ang_symm e c b] at hkey
      rw [ang_symm, ang_symm a c b]
      refine supplementary_congr ?_ ?_ hkey
      · rw [three_pt_ang_supplementary]; rw [between_symm] at habd
        exact ⟨habd, noncol13 hdbc, noncol13 habc⟩
      · rw [three_pt_ang_supplementary]; rw [between_symm] at hace
        exact ⟨hace, noncol13 hecb, noncol123 habc⟩

/-- I.6 in Elements: a triangle with two congruent base angles is isosceles. -/
theorem isosceles' {a b c : Pts} (habc : noncol a b c) :
    ((∠[a, b, c]) ≅ₐ (∠[a, c, b])) → ((a-ₛb) ≅ₛ (a-ₛc)) := by
      have key : ∀ {a b c : Pts}, noncol a b c → ((∠[a, b, c]) ≅ₐ (∠[a, c, b]))
          → ¬((a-ₛb) <ₛ (a-ₛc)) := by
        intro a b c habc he hf
        have hab := (noncol_neq habc).1
        have hbc := (noncol_neq habc).2.2
        rw [seg_symm a c, two_pt_seg_lt] at hf
        obtain ⟨d, hcda, habcd⟩ := hf
        have hcd := (between_neq hcda).1
        have had := (between_neq hcda).2.2.symm
        have hcdb := col_noncol (col23 (between_col hcda)) (noncol132 habc) hcd
        have hs1 : (b-ₛa) ≅ₛ (c-ₛd) := by rw [seg_symm]; exact habcd
        have hs2 : (b-ₛc) ≅ₛ (c-ₛb) := by rw [seg_symm]; exact seg_congr_refl _
        have ha : ∠[a, b, c] ≅ₐ ∠[d, c, b] := by
          rw [ang_symm d c b, ang_eq_same_side_pt b (between_same_side_pt.1 hcda).1, ang_symm b c a]
          exact he
        have htri : (Δ b a c) ≅ₜ (Δ c d b) := SAS (noncol12 habc) hcdb hs1 hs2 ha
        have hangle : ∠[d, b, c] ≅ₐ ∠[a, b, c] := by
          apply ang_congr_trans _ (ang_congr_symm he)
          rw [ang_symm, ang_symm a c b]
          exact ang_congr_symm (tri_congr_ang htri).2.2
        apply (ang_tri (ang_proper_iff_noncol.2 (noncol123 hcdb))
          (ang_proper_iff_noncol.2 habc)).2.1
        refine ⟨?_, hangle⟩
        rw [ang_symm a b c, three_pt_ang_lt]
        refine ⟨d, ?_, ?_⟩
        · rw [inside_three_pt_ang]
          refine ⟨t_shape_seg (noncol123 habc) d hcda, ?_⟩
          rw [between_symm] at hcda
          exact t_shape_seg (noncol12 habc) d hcda
        · rw [ang_symm]; exact ang_congr_refl _
      intro he
      have hab := (noncol_neq habc).1
      have hac := (noncol_neq habc).2.1
      rcases (seg_tri (seg_proper_iff_neq.2 hab) (seg_proper_iff_neq.2 hac)).1 with h | h | h
      · exact absurd h (key habc he)
      · exact h
      · exact absurd h (key (noncol23 habc) (ang_congr_symm he))

private lemma SSS_case1 {a b c d e : Pts} (habc : noncol a b c)
    (hbadbda : (∠[b, a, d]) ≅ₐ (∠[b, d, a])) (hcadcda : (∠[c, a, d]) ≅ₐ (∠[c, d, a]))
    (hdea : between d e a) (hebc : between e b c) : ∠[b, a, c] ≅ₐ ∠[b, d, c] := by
      have hda := (between_neq hdea).2.1
      have hae := (between_neq hdea).2.2.symm
      have hce := (between_neq hebc).2.1.symm
      have hbe := (between_neq hebc).1.symm
      have hcae := col_noncol (col13 (between_col hebc)) (noncol13 habc) hce
      have hbea := col_noncol (col123 (between_col hebc)) (noncol123 habc) hbe
      rw [ang_symm, ang_symm b d a] at hbadbda
      rw [ang_symm, ang_symm c d a] at hcadcda
      have hbin : inside_ang b (∠[d, a, c]) := by
        rw [ang_symm, ang_eq_same_side_pt c (between_same_side_pt.1 hdea).2]
        rw [between_symm] at hebc
        exact hypo_inside_ang (noncol23 hcae) hebc
      have hdabc : same_side_line (d-ₗa) b c := by
        rw [two_pt_one_line (line_in_lines hda) (line_in_lines hae) hae (pt_right_in_line d a)
          (col_in13 (between_col hdea) hda) (pt_left_in_line a e) (pt_right_in_line a e)]
        exact same_side_pt_line (between_same_side_pt.1 hebc).1 (line_in_lines hae)
          (pt_right_in_line a e) (noncol_in32 hbea) (noncol_in32 hcae)
      exact (congr_ang_sub hbin hdabc hda hcadcda hbadbda).2

private lemma SSS_case2 {a b c d e : Pts}
    (hcadcda : (∠[c, a, d]) ≅ₐ (∠[c, d, a])) (hdea : between d e a) (heb : e = b) :
    ∠[b, a, c] ≅ₐ ∠[b, d, c] := by
      rw [← heb, ang_symm e d c, ang_eq_same_side_pt c (between_same_side_pt.1 hdea).1, ang_symm,
        ← ang_eq_same_side_pt c (between_same_side_pt.1 hdea).2]
      exact hcadcda

private lemma SSS_case3 {a b c d e : Pts} (habc : noncol a b c)
    (hbadbda : (∠[b, a, d]) ≅ₐ (∠[b, d, a])) (hcadcda : (∠[c, a, d]) ≅ₐ (∠[c, d, a]))
    (hdea : between d e a) (hbec : between b e c) : ∠[b, a, c] ≅ₐ ∠[b, d, c] := by
      have hda := (between_neq hdea).2.1
      have hbe := (between_neq hbec).1
      have hce := (between_neq hbec).2.2.symm
      rw [ang_eq_same_side_pt _ (between_same_side_pt.1 hdea).2] at hbadbda
      rw [ang_symm c d a, ang_eq_same_side_pt c (between_same_side_pt.1 hdea).2,
        ang_symm c a e] at hcadcda
      have hbea := col_noncol (col23 (between_col hbec)) (noncol123 habc) hbe
      have hadb := col_noncol (col13 (between_col hdea)) (noncol13 hbea) hda.symm
      have hcea := col_noncol (col132 (between_col hbec)) (noncol13 habc) hce
      have hadc := col_noncol (col13 (between_col hdea)) (noncol13 hcea) hda.symm
      have hdin := hypo_inside_ang (noncol12 habc) hbec
      have hdabc := diff_side_pt_line (between_diff_side_pt.1 hbec) (line_in_lines hda)
        (col_in13 (between_col hdea) hda) (noncol_in21 hadb) (noncol_in21 hadc)
      exact (congr_ang_add hdin hdabc hda hbadbda hcadcda).2

/-- I.8 in Elements: SSS congruence of triangles. -/
theorem SSS {ABC DEF : triang} (habc : noncol ABC.v1 ABC.v2 ABC.v3)
    (ha'b'c' : noncol DEF.v1 DEF.v2 DEF.v3) (haba'b' : (ABC.v1-ₛABC.v2) ≅ₛ (DEF.v1-ₛDEF.v2))
    (haca'c' : (ABC.v1-ₛABC.v3) ≅ₛ (DEF.v1-ₛDEF.v3))
    (hbcb'c' : (ABC.v2-ₛABC.v3) ≅ₛ (DEF.v2-ₛDEF.v3)) : ABC ≅ₜ DEF := by
      obtain ⟨a, b, c⟩ := ABC
      obtain ⟨a', b', c'⟩ := DEF
      have hab := (noncol_neq habc).1
      have hac := (noncol_neq habc).2.1
      have hbc := (noncol_neq habc).2.2
      have ha'b' := (noncol_neq ha'b'c').1
      obtain ⟨d, ha'b'c'dbc, hbcda⟩ :=
        extend_congr_ang' (ang_proper_iff_noncol.2 ha'b'c') hbc (noncol_in23 habc)
      have hbd := (diff_side_line_neq hbcda).1.symm
      obtain ⟨d', hbdd', ha'b'bd, -⟩ := extend_congr_seg (seg_proper_iff_neq.2 ha'b') hbd
      replace hbcda := ray_diff_side_line hbc hbcda hbdd'
      rw [ang_symm d b c, ang_eq_same_side_pt c hbdd', ang_symm c b d'] at ha'b'c'dbc
      have had := (diff_side_line_neq'' hbcda).symm
      have hbcd := (diff_side_line_noncol hbcda hbc).1
      have hs1 : (b-ₛd') ≅ₛ (b'-ₛa') := by rw [seg_symm b' a']; exact seg_congr_symm ha'b'bd
      have htri1 : (Δ b d' c) ≅ₜ (Δ b' a' c') :=
        SAS (noncol23 hbcd) (noncol12 ha'b'c') hs1 hbcb'c' (ang_congr_symm ha'b'c'dbc)
      have hcacd : (c-ₛa) ≅ₛ (c-ₛd') := by
        rw [seg_symm, seg_symm c d']
        exact seg_congr_trans haca'c' (seg_congr_symm (tri_congr_seg htri1).2.2)
      have hbabd : (b-ₛa) ≅ₛ (b-ₛd') := by
        rw [seg_symm, seg_symm b d']
        exact seg_congr_trans haba'b' (seg_congr_symm (tri_congr_seg (tri_congr12 htri1)).1)
      obtain ⟨e, he⟩ := hbcda.1
      have hed : e ≠ d' := by intro hf; rw [hf] at he; exact noncol_in12 hbcd he.1
      have hea : e ≠ a := by intro hf; rw [hf] at he; exact noncol_in23 habc he.1
      have hdea := seg_in_neq hed hea he.2
      have ha_big : ∠[b, a, c] ≅ₐ ∠[b, d', c] := by
        by_cases heb : e = b
        · have hcad2 : noncol c a d' :=
            noncol132 (col_noncol (col13 (between_col (heb ▸ hdea))) habc had)
          exact SSS_case2 (isosceles hcad2 hcacd) hdea heb
        · have hbad : noncol b a d' := by
            intro hf
            apply heb
            refine two_line_one_pt (line_in_lines hbc) (line_in_lines had.symm) ?_ he.1
              ((seg_in_line d' a) he.2) (pt_left_in_line b c) (col_in32 hf had.symm)
            intro hf2; apply noncol_in23 habc; rw [hf2]; exact pt_right_in_line d' a
          have hbadbda := isosceles hbad hbabd
          by_cases hec : e = c
          · rw [ang_symm, ang_symm b d' c]
            exact SSS_case2 hbadbda hdea hec
          · have hcad : noncol c a d' := by
              intro hf
              apply hec
              refine two_line_one_pt (line_in_lines hbc) (line_in_lines had.symm) ?_ he.1
                ((seg_in_line d' a) he.2) (pt_right_in_line b c) (col_in32 hf had.symm)
              intro hf2; apply noncol_in23 habc; rw [hf2]; exact pt_right_in_line d' a
            have hcadcda := isosceles hcad hcacd
            rcases between_tri (col_in23' he.1) heb hec hbc with h | h | h
            · exact SSS_case1 habc hbadbda hcadcda hdea h
            · rw [ang_symm, ang_symm b d' c]
              exact SSS_case1 (noncol23 habc) hcadcda hbadbda hdea h
            · exact SSS_case3 habc hbadbda hcadcda hdea h
      have hs1f : (a-ₛb) ≅ₛ (d'-ₛb) := by
        apply seg_congr_trans haba'b'
        rw [seg_symm, seg_symm d' b]
        exact seg_congr_symm (tri_congr_seg htri1).1
      have hs2f : (a-ₛc) ≅ₛ (d'-ₛc) := by
        apply seg_congr_trans haca'c'
        exact seg_congr_symm (tri_congr_seg htri1).2.2
      have htri_final : (Δ a b c) ≅ₜ (Δ d' b c) := SAS habc (noncol132 hbcd) hs1f hs2f ha_big
      exact tri_congr12 (tri_congr_trans (tri_congr12 htri_final) htri1)

/-- Existence of an isosceles triangle on a given base, on the same side as `c`. -/
lemma isosceles_exist {a b c : Pts} (habc : noncol a b c) :
    ∃ d : Pts, ((a-ₛd) ≅ₛ (b-ₛd)) ∧ same_side_line (a-ₗb) c d := by
      have key : ∀ {a b c : Pts}, noncol a b c → ((∠[c, a, b]) <ₐ (∠[c, b, a]))
          → ∃ d : Pts, ((a-ₛd) ≅ₛ (b-ₛd)) ∧ same_side_line (a-ₗb) c d := by
        intro a b c habc h
        have hab := (noncol_neq habc).1
        have hbc := (noncol_neq habc).2.2
        rw [ang_symm c b a] at h
        obtain ⟨d, hdin, hd⟩ := three_pt_ang_lt.1 h
        obtain ⟨e, he⟩ := crossbar hdin
        have hae : a ≠ e := by
          intro hae; rw [← hae] at he
          apply noncol_in12 (ang_proper_iff_noncol.1 (inside_ang_proper' hdin).1)
          rw [line_symm]; exact ray_in_line b d he.1
        have haeb := col_noncol (col_in12' ((seg_in_line a c) he.2)) (noncol23 habc) hae
        have heb := (noncol_neq haeb).2.2
        have hbcd := (same_side_line_noncol (inside_three_pt_ang.1 hdin).2 hbc).2
        have hec : e ≠ c := by
          intro hf; rw [hf] at he; exact noncol_in13 hbcd ((ray_in_line b d) he.1)
        refine ⟨e, ?_, ?_⟩
        · rw [seg_symm, seg_symm b e]
          apply isosceles' (noncol12 haeb)
          rw [ang_symm, ← ang_eq_same_side_pt b (ray_in_neq hae.symm (seg_in_ray a c he.2))]
          rw [ang_symm e b a, ← ang_eq_same_side_pt a (ray_in_neq heb he.1)]
          rw [ang_symm]; exact ang_congr_symm hd
        · rw [line_symm]; exact t_shape_seg (noncol12 habc) e (seg_in_neq hae.symm hec he.2)
      rcases (ang_tri (ang_proper_iff_noncol.2 (noncol132 habc))
        (ang_proper_iff_noncol.2 (noncol13 habc))).1 with h | h | h
      · exact key habc h
      · exact ⟨c, by rw [seg_symm, seg_symm b c]; exact isosceles' (noncol132 habc) h,
          same_side_line_refl (noncol_in12 habc)⟩
      · obtain ⟨d, hd⟩ := key (noncol12 habc) h
        rw [line_symm] at hd
        exact ⟨d, seg_congr_symm hd.1, hd.2⟩

/-- Existence of an isosceles triangle on a given base, on the opposite side from `c`. -/
lemma isosceles_exist' {a b c : Pts} (habc : noncol a b c) :
    ∃ d : Pts, ((a-ₛd) ≅ₛ (b-ₛd)) ∧ diff_side_line (a-ₗb) c d := by
      obtain ⟨d, hcad⟩ := between_extend (noncol_neq habc).2.1.symm
      have habd := noncol23 (col_noncol (col12 (between_col hcad)) (noncol23 habc)
        (between_neq hcad).2.2)
      obtain ⟨e, he⟩ := isosceles_exist habd
      refine ⟨e, he.1, ?_⟩
      have hab := (noncol_neq habc).1
      apply diff_same_side_line (line_in_lines hab) _ he.2
      exact diff_side_pt_line (between_diff_side_pt.1 hcad) (line_in_lines hab)
        (pt_left_in_line a b) (noncol_in12 habc) (noncol_in12 habd)

private lemma ang_bisector_exist_prep {a b d e f : Pts} :
    ((a-ₛb) ≅ₛ (a-ₛd)) → ((b-ₛe) ≅ₛ (d-ₛe)) → diff_side_line (b-ₗd) a e → noncol b d a →
    between a f e → f ∈ (b-ₗd) ∩ (a-ₛe).inside → noncol a b e := by
      intro habad hbede he hbda hafe hf
      have had := (noncol_neq hbda).2.2.symm
      have hbd := (noncol_neq hbda).1
      have hae := (between_neq hafe).2.1
      apply noncol23
      apply col_noncol (between_col hafe)
      apply noncol13
      apply col_noncol (col_in12' hf.1) hbda
      · intro hbf
        rw [← hbf] at hafe
        obtain ⟨i, hadi⟩ := between_extend had
        have hdi := (between_neq hadi).2.2
        have hbdi := noncol132 (col_noncol (col12 (between_col hadi)) (noncol123 hbda)
          (between_neq hadi).2.2)
        have hbdibde : (∠[b, d, i]) ≅ₐ (∠[b, d, e]) := by
          rw [seg_symm, seg_symm d e] at hbede
          have hebd : noncol e b d := fun hebd => he.2.2 (col_in23 hebd hbd)
          rw [ang_symm b d e]
          apply ang_congr_trans _ (isosceles hebd hbede)
          rw [ang_symm e b d]
          have hbda_dba : (∠[b, d, a]) ≅ₐ (∠[d, b, a]) := by
            rw [ang_symm, ang_symm d b a]
            exact ang_congr_symm (isosceles (noncol132 hbda) habad)
          apply supplementary_congr _ _ hbda_dba
          · rw [three_pt_ang_supplementary]; exact ⟨hadi, hbda, hbdi⟩
          · rw [three_pt_ang_supplementary]; exact ⟨hafe, noncol12 hbda, noncol13 hebd⟩
        apply noncol13 hbda
        have hbdie : same_side_line (b-ₗd) i e := by
          apply diff_side_line_cancel (line_in_lines hbd) _ he
          exact diff_side_pt_line (diff_side_pt_symm (between_diff_side_pt.1 hadi))
            (line_in_lines hbd) (pt_right_in_line b d) (noncol_in12 hbdi) (noncol_in12 hbda)
        have hdie : col d i e := (ang_unique_same_side hbd hbdie hbdibde).2
        exact col_trans (col123 (col_trans (col123 (between_col hadi)) hdie hdi))
          (col23 (between_col hafe)) hae
      · exact hae

/-- I.9 in Elements: existence of the angle bisector. -/
lemma ang_bisector_exist {a b c : Pts} (hbac : ang_proper (∠[b, a, c])) :
    ∃ d : Pts, ((∠[b, a, d]) ≅ₐ (∠[c, a, d])) ∧ inside_ang d (∠[b, a, c]) := by
      rw [ang_proper_iff_noncol] at hbac
      have hab := (noncol_neq hbac).1.symm
      have hac := (noncol_neq hbac).2.2
      obtain ⟨d, hacd, habad, -⟩ := extend_congr_seg (seg_proper_iff_neq.2 hab) hac
      have had := (same_side_pt_neq hacd).2.symm
      have hbda := noncol13 (col_noncol hacd.2 (noncol123 hbac) had)
      have hbd := (noncol_neq hbda).1
      obtain ⟨e, hbede, he⟩ := isosceles_exist' hbda
      obtain ⟨f, hf⟩ := he.1
      have hfa : f ≠ a := by intro hfa; rw [hfa] at hf; exact absurd hf.1 (noncol_in12 hbda)
      have hfe : f ≠ e := by intro hfe; rw [hfe] at hf; exact absurd hf.1 he.2.2
      have hafe := seg_in_neq hfa hfe hf.2
      have habe := ang_bisector_exist_prep habad hbede he hbda hafe hf
      have hade : noncol a d e := by
        rw [line_symm] at he hf
        exact ang_bisector_exist_prep (seg_congr_symm habad) (seg_congr_symm hbede) he
          (noncol12 hbda) hafe hf
      have hbafcaf : (∠[b, a, f]) ≅ₐ (∠[c, a, f]) := by
        rw [ang_eq_same_side_pt b (between_same_side_pt.1 hafe).1,
          ang_eq_same_side_pt c (between_same_side_pt.1 hafe).1]
        rw [ang_symm c a e, ang_eq_same_side_pt e hacd, ang_symm e a d]
        exact (tri_congr_ang (SSS habe hade habad (seg_congr_refl _) hbede)).2.1
      refine ⟨f, hbafcaf, ?_⟩
      rw [ang_eq_same_side_pt b hacd]
      by_cases hbf : b = f
      · rw [← hbf] at hafe; exact absurd (between_col hafe) habe
      by_cases hdf : d = f
      · rw [← hdf] at hafe; exact absurd (between_col hafe) hade
      have hbdf := col_in12' hf.1
      have hbaf := noncol23 (col_noncol hbdf hbda hbf)
      have hdaf := noncol23 (col_noncol (col12 hbdf) (noncol12 hbda) hdf)
      rw [ang_symm c a f, ang_eq_same_side_pt f hacd, ang_symm f a d] at hbafcaf
      rcases between_tri (col_in12' hf.1) hbd hbf hdf with h | h | h
      · exfalso
        apply (ang_tri (ang_proper_iff_noncol.2 hbaf) (ang_proper_iff_noncol.2 hdaf)).2.2.2
        refine ⟨hbafcaf, ?_⟩
        rw [ang_symm b a f, three_pt_ang_lt]
        refine ⟨d, ?_, by rw [ang_symm]; exact ang_congr_refl _⟩
        rw [between_symm] at h
        exact hypo_inside_ang (noncol13 hbaf) h
      · exact hypo_inside_ang (noncol23 hbda) h
      · exfalso
        apply (ang_tri (ang_proper_iff_noncol.2 hbaf) (ang_proper_iff_noncol.2 hdaf)).2.1
        refine ⟨?_, hbafcaf⟩
        rw [ang_symm d a f, three_pt_ang_lt]
        refine ⟨b, ?_, by rw [ang_symm]; exact ang_congr_refl _⟩
        rw [between_symm] at h
        exact hypo_inside_ang (noncol13 hdaf) h

/-- I.10 in Elements: existence of the midpoint of a segment. -/
lemma midpt_exist {a b : Pts} (hab : a ≠ b) :
    ∃ c : Pts, between a c b ∧ ((a-ₛc) ≅ₛ (b-ₛc)) := by
      obtain ⟨c, habc⟩ := noncol_exist hab
      obtain ⟨d, hd, hcd⟩ := isosceles_exist habc
      have hadb := noncol23 (same_side_line_noncol hcd hab).2
      obtain ⟨e, he, hein⟩ := ang_bisector_exist (ang_proper_iff_noncol.2 hadb)
      obtain ⟨f, hf⟩ := crossbar hein
      have hfa : f ≠ a := by
        intro hfa; rw [hfa] at hf
        exact noncol_in12 (noncol12 (ang_proper_iff_noncol.1 (inside_ang_proper' hein).1))
          ((ray_in_line d e) hf.1)
      have hfb : f ≠ b := by
        intro hfb; rw [hfb] at hf
        exact noncol_in12 (noncol12 (ang_proper_iff_noncol.1 (inside_ang_proper' hein).2))
          ((ray_in_line d e) hf.1)
      have h := seg_in_neq hfa hfb hf.2
      refine ⟨f, h, ?_⟩
      have htri : (Δ d a f) ≅ₜ (Δ d b f) := by
        have hsspt : same_side_pt d e f := by
          rcases hf.1 with hf' | hf'
          · exact hf'
          · simp only [Set.mem_singleton_iff] at hf'
            rw [hf'] at h; exact absurd (between_col h) hadb
        rw [ang_eq_same_side_pt a hsspt, ang_eq_same_side_pt b hsspt] at he
        have hs1 : (d-ₛa) ≅ₛ (d-ₛb) := by rw [seg_symm, seg_symm d b]; exact hd
        exact SAS
          (noncol132 (col_noncol (col23 (between_col h)) (noncol23 hadb) (between_neq h).1))
          (noncol132 (col_noncol (col132 (between_col h)) (noncol132 hadb)
            (between_neq h).2.2.symm))
          hs1 (seg_congr_refl _) he
      exact (tri_congr_seg htri).2.2

private lemma ang_exter_lt_inter_prep {a b c d : Pts} (habc : noncol a b c)
    (hbcd : between b c d) : ∠[b, a, c] <ₐ ∠[a, c, d] := by
      have hac := (noncol_neq habc).2.1
      have hcd := (between_neq hbcd).2.2
      have hbc := (noncol_neq habc).2.2
      have hcda := col_noncol (col12 (between_col hbcd)) (noncol13 habc) hcd
      obtain ⟨e, haec, he⟩ := midpt_exist hac
      have hae := (between_neq haec).1
      have hbe : b ≠ e := by intro hbe; rw [← hbe] at haec; exact habc (between_col haec)
      have hec := (between_neq haec).2.2
      obtain ⟨f, hbef, hf, -⟩ := extend_congr_seg' (seg_proper_iff_neq.2 hbe) hbe.symm
      rw [← between_diff_side_pt] at hbef
      have hef := (between_neq hbef).2.2
      have hceb := col_noncol (col132 (between_col haec)) (noncol132 habc) hec.symm
      have hefc := col_noncol (col12 (between_col hbef)) (noncol123 hceb) hef
      have hcaf := col_noncol (col13 (between_col haec)) (noncol132 hefc) hac.symm
      have haeb := col_noncol (col23 (between_col haec)) (noncol23 habc) hae
      rw [three_pt_ang_lt]
      refine ⟨f, ?_, ?_⟩
      · rw [inside_three_pt_ang]
        have hd1 : diff_side_line (c-ₗa) d b :=
          diff_side_line_symm (diff_side_pt_line (between_diff_side_pt.1 hbcd)
            (line_in_lines hac.symm) (pt_left_in_line c a) (noncol_in13 (noncol13 habc))
            (noncol_in13 hcda))
        have hd2 : diff_side_line (c-ₗa) b f :=
          diff_side_pt_line (between_diff_side_pt.1 hbef) (line_in_lines hac.symm)
            (col_in13 (col13 (between_col haec)) hac.symm) (noncol_in13 (noncol13 habc))
            (noncol_in12 hcaf)
        refine ⟨diff_side_line_cancel (line_in_lines hac.symm) hd1 hd2, ?_⟩
        have hae_part : same_side_line (c-ₗd) a e := by
          rw [line_symm]; exact t_shape_seg (noncol12 hcda) e ((between_symm a e c).1 haec)
        have hef_part : same_side_line (c-ₗd) e f := by
          rw [two_pt_one_line (line_in_lines hcd) (line_in_lines hbc) hbc
            (col_in23 (between_col hbcd) hcd) (pt_left_in_line c d) (pt_left_in_line b c)
            (pt_right_in_line b c), line_symm]
          exact t_shape_ray (noncol23 hceb) (between_same_side_pt.1 hbef).1
        exact same_side_line_trans (line_in_lines hcd) hae_part hef_part
      · have hs1 : (e-ₛa) ≅ₛ (e-ₛc) := by rw [seg_symm, seg_symm e c]; exact he
        have hs2 : (e-ₛb) ≅ₛ (e-ₛf) := by rw [seg_symm]; exact hf
        have htri : (Δ e a b) ≅ₜ (Δ e c f) :=
          SAS (noncol12 haeb) (noncol23 hefc) hs1 hs2 (vertical_ang_congr haeb haec hbef)
        rw [ang_symm, ang_eq_same_side_pt f (between_same_side_pt.1 haec).2,
          ← ang_eq_same_side_pt b (between_same_side_pt.1 haec).1, ang_symm, ang_symm b a e]
        exact ang_congr_symm (tri_congr_ang htri).1

/-- I.16 in Elements: each remote interior angle is less than the exterior angle. -/
lemma ang_exter_lt_inter {a b c d : Pts} (habc : noncol a b c) (hbcd : between b c d) :
    (∠[b, a, c] <ₐ ∠[a, c, d]) ∧ (∠[a, b, c] <ₐ ∠[a, c, d]) := by
      refine ⟨ang_exter_lt_inter_prep habc hbcd, ?_⟩
      have hac := (noncol_neq habc).2.1
      have hcd := (between_neq hbcd).2.2
      have hcda := col_noncol (col12 (between_col hbcd)) (noncol13 habc) hcd
      obtain ⟨e, hace⟩ := between_extend hac
      refine (ang_lt_congr ?_).2 (ang_proper_iff_noncol.2 (noncol132 hcda))
        (ang_exter_lt_inter_prep (noncol12 habc) hace)
      rw [ang_symm]
      have hce := (between_neq hace).2.2
      exact vertical_ang_congr
        (noncol12 (col_noncol (col12 (between_col hace)) (noncol132 habc) hce))
        ((between_symm a c e).1 hace) hbcd

/-- I.18 in Elements: the angle opposite the greater side is the greater angle.
Here `(a-ₛb) <ₛ (a-ₛc)` (side `ab` shorter than side `ac`) implies `∠[a, c, b] <ₐ ∠[a, b, c]`
(the angle at `c`, opposite `ab`, is smaller than the angle at `b`, opposite `ac`). -/
lemma greater_side_ang {a b c : Pts} (habc : noncol a b c) (hs : (a-ₛb) <ₛ (a-ₛc)) :
    ∠[a, c, b] <ₐ ∠[a, b, c] := by
      have hab := (noncol_neq habc).1
      have hbc := (noncol_neq habc).2.2
      obtain ⟨d, hadc, habad⟩ := two_pt_seg_lt.1 hs
      have had := (between_neq hadc).1
      have hcd := (between_neq hadc).2.2.symm
      apply ang_lt_trans (ang_proper_iff_noncol.2 (noncol23 habc))
      · rw [ang_symm, ang_eq_same_side_pt b (between_same_side_pt.1 hadc).2]
        rw [between_symm] at hadc
        apply (ang_exter_lt_inter ?_ hadc).2
        exact noncol132 (col_noncol (col23 (between_col hadc)) (noncol132 habc) hcd)
      · apply (ang_lt_congr (show (∠[a, d, b]) ≅ₐ (∠[b, d, a]) from by
          rw [ang_symm]; exact ang_congr_refl _)).1
        rw [three_pt_ang_lt]
        refine ⟨d, hypo_inside_ang habc hadc, ?_⟩
        exact isosceles
          (noncol23 (col_noncol (col23 (between_col hadc)) (noncol23 habc) had)) habad

/-- The angle–side inequality in the labelling of the user's prompt: in triangle `abc`, if
`AB > AC` — formalised as the side `ac` being shorter than the side `ab`, `(a-ₛc) <ₛ (a-ₛb)` —
then `∠ACB > ∠ABC`, formalised as `∠[a, b, c] <ₐ ∠[a, c, b]`. This is `greater_side_ang`
(Euclid I.18) with the roles of `b` and `c` exchanged. -/
lemma ang_opposite_greater_side {a b c : Pts} (habc : noncol a b c)
    (hs : (a-ₛc) <ₛ (a-ₛb)) : ∠[a, b, c] <ₐ ∠[a, c, b] :=
  greater_side_ang (noncol23 habc) hs

end Hilbert
