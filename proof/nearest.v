(* We don't need this at present but it might come in useful someday *)

From Stdlib Require Import ZArith Bool Reals Psatz.
From Flocq.Core Require Import Raux Generic_fmt FLX FLT Ulp Round_NE Zaux.
From Flocq Require Import BinarySingleNaN Binary Bits.
Import Defs.

Section Floats.
 Variable precp: positive.
 Let prec := Z.pos precp.
 Variable emax : Z.
 Variable prec_gt_1: (1<prec)%Z.
 Local Instance prec_gt_0: Prec_gt_0 prec := eq_refl _.
 Variable (prec_lt_emax_bool : is_true (Z.ltb prec emax)).
 Local Instance Hprec_emax: Prec_lt_emax prec emax := proj1 (Z.ltb_lt _ _) prec_lt_emax_bool.
 Let  emin := (3 - emax - prec)%Z.
 Let fexp := FLT_exp emin prec.
 Let choice := fun x : Z => negb (Z.even x).
 Variable Hemax: (3 <= emax)%Z.

Lemma round_lemma:  (* adapted from libValidSDP.binary_infnan.firnd_spec *)
 forall   (x: R),
 let xn := binary_normalize prec emax _ _ mode_NE
       (round_mode mode_NE (scaled_mantissa radix2 fexp x)) 
       (cexp radix2 fexp x) false
  in is_finite _ _ xn = true -> 
   B2R prec emax xn = 
   round radix2 (FLT_exp (3 - emax - Z.pos precp) (Z.pos precp)) (Znearest choice) x.
Proof.
intro x.
set (mx := round_mode mode_NE (scaled_mantissa radix2 fexp x)).
set (ex := cexp radix2 fexp x).
intros xn FIN.
assert (H := binary_normalize_correct prec emax _ _ mode_NE mx ex false).
fold xn in H.
destruct (Rlt_bool _ _) eqn:?H in H.
-
destruct H as [H _]. rewrite H; clear H.
rewrite round_generic; auto.
apply valid_rnd_N.
apply generic_format_round; [apply FLT_exp_valid|apply valid_rnd_N].
red. lia.
 -
destruct xn; discriminate.
Qed.


Lemma is_finite_round: forall x,
  (is_finite prec emax x = true) ->
 (Rabs
   (Generic_fmt.round radix2 (SpecFloat.fexp prec emax) (round_mode mode_NE)
      (IZR (round_mode mode_NE (scaled_mantissa radix2 fexp (B2R prec emax x))) *
       bpow radix2 (cexp radix2 fexp (B2R prec emax x)))) <
  bpow radix2 emax)%R.
Proof.
intros x FIN.
assert (nan : {x : binary_float prec emax | is_nan prec emax x = true}). {
  assert (nan_pl prec 1 = true) by (unfold nan_pl; simpl; lia).
 exists (B754_nan prec emax false 1%positive H); reflexivity.
}
pose (abs_nan := fun _ :  binary_float prec emax  => nan).
pose proof scaled_mantissa_generic radix2 fexp (B2R prec emax x) (generic_format_B2R _ _  x).
rewrite H.
rewrite <- round_NE_abs by (apply fexp_correct; red; lia).
rewrite Rabs_mult.
rewrite Rabs_Zabs.
rewrite Rabs_pos_eq by apply bpow_ge_0.
set (sm := scaled_mantissa _ _ _) in H|-*.
unfold round, F2R, Fnum, Fexp.
unfold round_mode.
unfold Znearest.
rewrite Zfloor_IZR.
rewrite Rminus_diag.
rewrite Zceil_IZR.
change (SpecFloat.fexp _ _) with fexp.
assert (H02: Rcompare 0 (/2) = Lt). {
  clear. rewrite <- (Rmult_1_l (/2)). fold (Rdiv 1 2). rewrite (Rcompare_half_r 0 1). rewrite Rmult_0_r.
 rewrite Rcompare_IZR; auto.
}
rewrite H02.
rewrite <- Ztrunc_abs.
unfold sm; rewrite <- scaled_mantissa_abs.
rewrite <- cexp_abs.
rewrite <- (B2R_Babs prec emax abs_nan).
assert (Bsign prec emax (Babs prec emax abs_nan x) = false). {
 apply Bsign_Babs. clear - FIN; destruct x; auto; discriminate.
}
rewrite <- (is_finite_Babs _ _ abs_nan) in FIN.
clear H sm.
set (y := Babs _ _ _ _) in FIN,H0|-*.
clearbody y. clear x. clear nan abs_nan. rename y into x.
pose proof scaled_mantissa_generic radix2 fexp (B2R prec emax x) (generic_format_B2R _ _  _).
rewrite <- H.
rewrite scaled_mantissa_mult_bpow.
rewrite H.
rewrite Zceil_IZR, Zfloor_IZR.
rewrite Rminus_diag.
rewrite H02.
rewrite <- H.
rewrite scaled_mantissa_mult_bpow.
replace (B2R prec emax x) with (Rabs (B2R prec emax x)).
2:{ apply Rabs_pos_eq.
destruct x; try destruct s; try discriminate; simpl; try lra.
unfold F2R, Fnum, Fexp. apply Rmult_le_pos. apply IZR_le; lia.
apply bpow_ge_0.
}
apply abs_B2R_lt_emax.
Qed.


Definition R2B (x: R) : binary_float prec emax :=
  binary_normalize
    prec emax _ _
    BinarySingleNaN.mode_NE
    (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE
           (Generic_fmt.scaled_mantissa Zaux.radix2 (SpecFloat.fexp prec emax) x))
    (Generic_fmt.cexp Zaux.radix2 (SpecFloat.fexp prec emax) x)
    false.

Lemma B2R_R2B_B2R: forall (x: binary_float prec emax), is_finite _ _ x = true -> 
   B2R _ _ (R2B (B2R _ _ x)) = B2R _ _ x.
Proof.
intros x FIN.
unfold R2B. rewrite round_lemma; auto.
apply round_generic.
apply valid_rnd_N.
apply generic_format_FLT.
apply FLT_format_B2R.
red. lia.
assert (H := binary_normalize_correct prec emax _ _ mode_NE
   (round_mode mode_NE (scaled_mantissa radix2 fexp (B2R prec emax x)))
  (cexp radix2 fexp (B2R prec emax x)) false).
match type of H with if Rlt_bool ?A ?B then _ else _ => destruct (Rlt_bool_spec A B) end.
apply H.
exfalso.
clear H.
unfold F2R, Fnum, Fexp in H0.
revert H0; apply RIneq.Rlt_not_le.
change (FLT_exp _ _) with fexp.
apply is_finite_round; auto.
Qed.
 
Lemma R2B_lem2: forall (x: R), (Rabs x <= B2R prec emax (Bmax_float prec emax _ _))%R ->  
    B2R _ _ (R2B x) = round radix2 fexp ZnearestE  x.
Proof.
intros.
unfold R2B.
apply round_lemma.
assert (H0 := binary_normalize_correct prec emax _ _ mode_NE
   (round_mode mode_NE (scaled_mantissa radix2 fexp x))
  (cexp radix2 fexp x) false).
match type of H0 with if Rlt_bool ?A ?B then _ else _ => destruct (Rlt_bool_spec A B) end.
apply H0.
clear H0.
exfalso.
revert H1; apply RIneq.Rlt_not_le.
unfold F2R, Fnum, Fexp.
change (SpecFloat.fexp _ _) with fexp.
simpl in H. unfold F2R, Fnum, Fexp in H.
Abort.  (* Not clear if we actually need this *)

End Floats.

