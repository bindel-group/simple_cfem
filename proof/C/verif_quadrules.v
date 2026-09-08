Require Export VST.floyd.proofauto.
From vcfloat Require Export FPStdCompCert FPStdLib.
From LAProof.accuracy_proofs Require Export solve_model.
From LAProof.C Require Export floatlib.
From Stdlib Require Export Classes.RelationClasses.

From mathcomp Require (*Import*) ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require (*Import*) fintype finfun bigop finset fingroup perm order.
From mathcomp Require (*Import*) div ssralg countalg finalg zmodp matrix.
From mathcomp.zify Require Export ssrZ zify.
Import fintype matrix.

(** Now we undo all the settings that mathcomp has modified *)
Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Open Scope logic.

From CFEM.C Require Import quadrules.
Require Export CFEM.C.spec_quadrules.

Import quadmodel_accuracy.Quadmodel_F64.

Definition quadrules_E : funspecs := [].
Definition quadrules_internal_specs : funspecs := quadrules_ASI.
Definition quadrules_imported_specs : funspecs := [].
Definition quadrules_globals gv : mpred:= gauss_pts_pred gv.

Definition Gprog := quadrules_imported_specs ++ quadrules_internal_specs.

Lemma divs_repr: forall i j, 
  Int.min_signed <= i <= Int.max_signed ->
  Int.min_signed <= j <= Int.max_signed -> 
  Int.divs (Int.repr i) (Int.repr j) = Int.repr (i ÷ j).
Proof.
intros.
unfold Int.divs.
f_equal. f_equal; apply Int.signed_repr; auto.
Qed.

Lemma body_gauss_point: semax_body Vprog Gprog f_gauss_point gauss_point_spec_lowlevel.
Proof.
start_function.
unfold gauss_pts_pred.
assert (0 <= npts * (npts-1) <= 90) by nia.
assert (0 <= npts * (npts - 1) ÷ 2  <= 45 ). {
  split. apply Z.quot_pos; lia. apply (Z.quot_le_mono _ 90 2); lia.
}
assert (0 <=
Int.signed
  (Int.add (Int.divs (Int.repr (npts * (npts - 1))) (Int.repr 2))
     (Int.repr i)) <
Zlength gauss_pts_list). {
set (j := Zlength _); compute in j; subst j.
rewrite divs_repr; try rep_lia.
rewrite add_repr. rewrite Int.signed_repr; try rep_lia.
}
forward.
-
rewrite Znth_map by auto.
entailer!!.
-
entailer!!.
split.
rewrite divs_repr; try rep_lia.
rewrite Int.signed_repr; try rep_lia.
intros [? ?]. inv H5.
-
change (Zlength _) with 55 in H3.
rewrite divs_repr in H3|-*; try rep_lia.
rewrite add_repr in H3|-*.
rewrite Int.signed_repr in H3|-*; try rep_lia.
rewrite Znth_map by auto.
forward.
clear - H0 H.
apply prop_right. 
f_equal. f_equal. f_equal. 
apply Zquot.Zquot_Zdiv_pos; nia.
Qed.

Lemma body_gauss_weight: semax_body Vprog Gprog f_gauss_weight gauss_weight_spec_lowlevel.
Proof.
start_function.
unfold gauss_wts_pred.
assert (0 <= npts * (npts-1) <= 90) by nia.
assert (0 <= npts * (npts - 1) ÷ 2  <= 45 ). {
  split. apply Z.quot_pos; lia. apply (Z.quot_le_mono _ 90 2); lia.
}
assert (0 <=
Int.signed
  (Int.add (Int.divs (Int.repr (npts * (npts - 1))) (Int.repr 2))
     (Int.repr i)) <
Zlength gauss_wts_list). {
set (j := Zlength _); compute in j; subst j.
rewrite divs_repr; try rep_lia.
rewrite add_repr. rewrite Int.signed_repr; try rep_lia.
}
forward.
-
rewrite Znth_map by auto.
entailer!!.
-
entailer!!.
split.
rewrite divs_repr; try rep_lia.
rewrite Int.signed_repr; try rep_lia.
intros [? ?]. inv H5.
-
change (Zlength _) with 55 in H3.
rewrite divs_repr in H3|-*; try rep_lia.
rewrite add_repr in H3|-*.
rewrite Int.signed_repr in H3|-*; try rep_lia.
rewrite Znth_map by auto.
forward.
clear - H0 H.
apply prop_right. 
f_equal. f_equal. f_equal. 
apply Zquot.Zquot_Zdiv_pos; nia.
Qed.

Lemma body_gauss2d_npoint1d: semax_body Vprog Gprog f_gauss2d_npoint1d gauss2d_npoint1d_spec.
Proof.
start_function.
assert (repable_signed (s*s)).  (* See https://github.com/PrincetonUniversity/VST/issues/858  *)
  unfold repable_signed, Int.min_signed, Int.max_signed, Int.half_modulus, Int.modulus, Int.wordsize.
  simpl. nia. 
forward_if False.
1-5: forward; entailer!!; f_equal; f_equal; nia.
rewrite !Int.unsigned_repr in NE,NE0,NE1,NE2,NE3 by rep_lia.
exfalso.
destruct s; try nia.
destruct p; try nia.
Qed.

Lemma body_gauss2d_point: semax_body Vprog Gprog f_gauss2d_point gauss2d_point_spec.
Proof.
start_function.
forward_call (Z.of_nat n).
entailer!!. simpl. f_equal. f_equal. f_equal. lia.
destruct n as [n Hn]; simpl.
pose proof (@ssrnat.ltP n 5). rewrite Hn in H. inv H.
destruct x as [x Hx]. simpl in Hx.
pose proof (@ssrnat.ltP x n). rewrite Hx in H. inv H. lia.
destruct n as [n Hn].
pose proof (@ssrnat.ltP n 5). rewrite Hn in H. inv H.
destruct x as [x Hx].
pose proof (@ssrnat.ltP x n). simpl in Hx; rewrite Hx in H. inv H.
destruct y as [y Hy].
pose proof (@ssrnat.ltP y n). simpl in Hy; rewrite Hy in H. inv H.
assert (H3: 0 <= Z.of_nat (y * n + x) <= 25) by nia.
forward.
entailer!!.
split.
intro H'; apply repr_inj_signed in H';  rep_lia.
intros [? ?].
apply repr_inj_signed in H; try rep_lia.
forward.
entailer!!.
split.
intro H'; apply repr_inj_signed in H';  rep_lia.
intros [? ?].
apply repr_inj_signed in H; try rep_lia.
simpl nat_of_ord.
rewrite divs_repr; try rep_lia.
rewrite mods_repr; try rep_lia.
pose (X := existT (fun n => 'I_(nat_of_ord n)) (Ordinal  Hn) (Ordinal Hx)).
forward_call (X, gv); clear X.
entailer!!.
simpl. f_equal. f_equal. f_equal.
rewrite <- Nat2Z.inj_mod. f_equal.
rewrite Nat.Div0.add_mod, Nat.Div0.mul_mod, Nat.Div0.mod_same, Nat.mul_0_r, Nat.Div0.mod_0_l, Nat.add_0_l.
rewrite Nat.Div0.mod_mod, Nat.mod_small; lia.
Intros x'.
forward.
pose (X := existT (fun n => 'I_(nat_of_ord n)) (Ordinal  Hn) (Ordinal Hy)).
forward_call (X,gv); clear X.
entailer!!.
simpl. f_equal. f_equal. f_equal.
rewrite Nat2Z.inj_add, Nat2Z.inj_mul.
rewrite Z.quot_add_l; try lia.
rewrite Z.quot_small; try lia.
Intros y'.
forward.
Exists x' y'.
entailer!!.
Qed.

Lemma body_gauss2d_weight: semax_body Vprog Gprog f_gauss2d_weight gauss2d_weight_spec.
Proof.
start_function.
destruct n as [n Hn]; destruct i as [i Hi]; destruct j as [j Hj]; simpl in Hn, Hi, Hj; simpl Z.of_nat.
forward_call (Z.of_nat n).
entailer!!. simpl. f_equal. f_equal. f_equal. lia.
assert (H3: 0 <= Z.of_nat (j * n + i) <= 25) by nia. 
forward.
entailer!!.
split.
intro H'; apply repr_inj_signed in H';  rep_lia.
intros [? ?].
apply repr_inj_signed in H; try rep_lia.
forward.
entailer!!.
split.
intro H'; apply repr_inj_signed in H';  rep_lia.
intros [? ?].
apply repr_inj_signed in H; try rep_lia.
simpl nat_of_ord.
rewrite divs_repr; try rep_lia.
rewrite mods_repr; try rep_lia.
pose (X := existT (fun n => 'I_(nat_of_ord n)) (Ordinal  Hn) (Ordinal Hi)).
forward_call (X, gv); clear X.
entailer!!.
simpl. f_equal. f_equal. f_equal.
rewrite <- Nat2Z.inj_mod. f_equal.
rewrite Nat.Div0.add_mod, Nat.Div0.mul_mod, Nat.Div0.mod_same, Nat.mul_0_r, Nat.Div0.mod_0_l, Nat.add_0_l.
rewrite Nat.Div0.mod_mod, Nat.mod_small; lia.
Intros x'.
pose (X := existT (fun n => 'I_(nat_of_ord n)) (Ordinal  Hn) (Ordinal Hj)).
forward_call (X,gv); clear X.
entailer!!.
simpl. f_equal. f_equal. f_equal.
rewrite Nat2Z.inj_add, Nat2Z.inj_mul.
rewrite Z.quot_add_l; try lia.
rewrite Z.quot_small; try lia.
Intros y'.
forward.
Exists x' y'.
entailer!!.
Qed.


Lemma body_hughes_point: semax_body Vprog Gprog f_hughes_point hughes_point_spec.
Proof.
start_function.
destruct i as [i Hi]. simpl.
forward_if False.
1,2,3:
forward; forward; forward;
do 2 EExists; entailer!!; [ | apply derives_refl]; simpl nat_of_ord; rewrite E; unfold Znth; simpl; f_equal;
unfold FT2R;
with_strategy transparent [Float.of_bits] simpl; compute; Lra.lra.
rewrite !Int.unsigned_repr in *; try rep_lia.
Qed.


Import Rdefinitions Rbasic_fun.

Lemma body_hughes_weight: semax_body Vprog Gprog f_hughes_weight hughes_weight_spec.
Proof.
start_function.
forward.
EExists.
entailer!!.
red. 
change Float.div with (@BDIV _ Tdouble).
with_strategy transparent [Float.of_bits] unfold Float.of_bits.
rewrite !Int64.unsigned_repr by rep_lia.
set (d := half_an_ulp); hnf in d; simpl in d; subst d.
set (x := (_ / _)%F64).
unfold Bits.b64_of_bits, Bits.binary_float_of_bits, Binary.FF2B in x.
simpl in x.
hnf in x.
revert x.
set (H := proj1 _). clearbody H. simpl in H.
simpl.
unfold Defs.F2R, Defs.Fnum, Defs.Fexp.
unfold hughes_weight.
rewrite (Rabs_right (_ * _)%R).
2: compute; Lra.nra.
rewrite Rabs_left; compute; Lra.lra.
Qed.



















