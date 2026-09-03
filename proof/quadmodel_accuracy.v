Module Nearest.
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
End Nearest.


From mathcomp Require Import all_boot ssralg ssrnum archimedean finfun order.
From mathcomp Require Import all_algebra  all_field all_analysis all_reals.
Import Order.TTheory GRing.Theory. (*  Num.Theory. *)
From mathcomp.algebra_tactics Require Import ring lra.
Import classical_sets.
Import numFieldNormedType.Exports.
From Stdlib Require Import FunctionalExtensionality.
From CFEM Require Import quadrature quadrature2. Import Legendre.
Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Local Open Scope R_scope.
Local Open Scope order_scope.
Local Open Scope ring_scope.

Require Import Lia.

From libValidSDP Require Import misc fsum fsum_l2r float_infnan_spec.
Import Rbasic_fun.
Import Rstruct.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Local Notation R := (RbaseSymbolsImpl_R__canonical__reals_Real).

Import Interval.Tactic.

From Stdlib Require Import ProofIrrelevance.

Lemma FS_val_ext: forall {format} x y, 
  @float_spec.FS_val format x = float_spec.FS_val y -> x = y.
Proof.
intros.
destruct x,y; simpl in *.
subst FS_val0.
f_equal.
apply proof_irrelevance.
Qed.


Section FLOAT.
 
 Variable FI: Float_infnan_spec.
 Let fs := fis FI.

Notation F := (FIS FI).
Notation frnd := (frnd fs).
Notation eps := (eps fs).
Notation eta := (eta fs).
Variable n: 'I_5.

 Variable gauss_pt_f: forall (i: 'I_n), F.
 Variable gauss_wt_f: forall (i: 'I_n), F.

 Variable gauss_pt_f_range: forall i, Rdefinitions.Rle (Rabs (FIS2FS (gauss_pt_f i))) 1.

 Lemma gauss_pt_range: forall i, Rdefinitions.Rle (Rabs (quadrature2.gauss_pt n i)) 1.
 Proof.
 intros. pose proof (quadrature2.gauss_pt_range n i).
 prepare_for_interval.
 unfold Rabs. destruct (Rcase_abs _); Lra.lra.
Qed. 

 Definition gauss_pt (i: 'I_n) : bounded 1 := Build_bounded (gauss_pt_range i).

 Lemma gauss_wt_range: forall i, Rdefinitions.Rle (Rabs (quadrature2.gauss_wt n i)) 2.
 Proof.
 intros. pose proof (quadrature2.gauss_wt_range n i).
 prepare_for_interval.  set a := gauss_wt _ _ in H|-*. clearbody a.
 destruct H.
 unfold Rabs. destruct (Rcase_abs _); try Lra.lra. interval.
Qed.


 Definition gauss_wt (i: 'I_n) : bounded 2 := Build_bounded (gauss_wt_range i).
 
 Variable gauss_pts_err: forall (i: 'I_n),  finite (gauss_pt_f i) /\ Rabs (FS_val (FIS2FS (gauss_pt_f i)) - bounded_val (gauss_pt i)) <= eps.
 Variable gauss_wts_err: forall (i: 'I_n), finite (gauss_wt_f i) /\  Rabs (FS_val (FIS2FS (gauss_wt_f i)) - bounded_val (gauss_wt i)) <= eps.

 Variable (fb: R).
 Variable(g: R -> R).
 Variable Hg: forall x, -1 <= x <= 1 -> Rabs (g x) <= fb.
 Variable (b: R) (Hb: quadrature_error_bound g n b).
 Variable (d: R) (Hd: deriv_bound g d).

  Lemma g_max_deriv: forall x y, -1 <= x <= 1 -> -1 <= y <= 1 -> Rabs (g(x+y) - g x) <= Rabs y * d.
 Admitted.

 Variable (f: F -> F)  (f_acc: R).
 Variable (fun_acc: forall (x: F), finite x /\ -1 <= FS_val (FIS2FS x) <= 1 -> 
             finite (f x) /\   Rdefinitions.Rle (Rabs (FS_val (FIS2FS (f x)) - g (FS_val (FIS2FS x)))) f_acc).
 
 Definition parameter_limits : Prop := 
  (1 + n.-1%:R * (eps / (1 + eps))) * 
     (n%:R * ((1 + eps / (1 + eps)) * ((2 + eps) * (fb + f_acc)) + eta)) < m FI.

 Variable fb_limit:  parameter_limits. 

 Lemma fb_limit_simple: 
     (n%:R * ((1 + eps / (1 + eps)) * ((2 + eps) * (fb + f_acc)) + eta)) < m FI.
 Admitted.

Fixpoint fisum_l2r_rec [n] (c : F) : F^n -> F :=
  match n with
    | 0%N => fun _ => c
    | n'.+1 =>
      fun a => fisum_l2r_rec (fiplus c (a ord0)) [ffun i => a (lift ord0 i)]
  end.

Definition fisum_l2r [n] : F^n -> F :=
  match n with
    | 0%N => fun _ => FIS0 fs
    | n'.+1 =>
      fun a => fisum_l2r_rec (a ord0) [ffun i => a (lift ord0 i)]
  end.

Lemma finite_fisuml2r_recE: forall [n] c (xs: F^n), finite (fisum_l2r_rec c xs) -> finite c.
Proof.
clear.
move => n.
elim: n; auto.
clear n.
move => n IHn c xs FIN.
apply IHn in FIN.
apply fiplus_spec_fl in FIN.
auto.
Qed.

Lemma fisum_fsum: forall n (xs: F^n), finite (fisum_l2r xs) -> 
   fsum_l2r [ffun i => FIS2FS (xs i)] =FIS2FS (fisum_l2r xs).
Proof.
clear.
rewrite /fsum_l2r /fisum_l2r /reverse_coercion.
move => k.
case: k; [intros; apply FS_val_ext; rewrite FIS2FS0 // | ].
move => n xs.
rewrite ffunE.
set c := xs ord0.
set ci := FIS2FS c.
assert (ci = FIS2FS c) by reflexivity.
clearbody c. clearbody ci.
pose xs' := [ffun i => xs (rshift 1 i)].
rewrite (_: [ffun i => xs (lift ord0 i)] = xs'); 
  [ | apply eq_dffun => i; rewrite rshift1 //].
rewrite (_:  [ffun i => [ffun i0 => FIS2FS (xs i0)]  (lift ord0 i)] = [ffun i => FIS2FS (xs' i)]);
  [ | apply eq_dffun => i; rewrite ?ffunE rshift1 //].
simpl in xs'.
clearbody xs'. clear xs. rename xs' into xs.
move :c ci H xs; elim n; auto.
clear n.
move => n IHn c ci H xs.
rewrite /= ?ffunE.
pose xs' := [ffun i => xs (rshift 1 i)].
rewrite (_: [ffun i => xs (lift ord0 i)] = xs'); 
  [ | apply eq_dffun => i; rewrite rshift1 //].
rewrite (_: [ffun i => [ffun i' => FIS2FS (xs i')] (lift ord0 i)] = [ffun i => FIS2FS (xs' i)]);
  [ | apply eq_dffun => i; rewrite /xs'  ?ffunE rshift1 //].
move => FIN.
apply IHn; auto.
subst ci.
apply FS_val_ext.
rewrite  fiplus_spec //.
apply finite_fisuml2r_recE in FIN; auto.
Qed.


 Definition integrate_model_f  : F :=
     fisum_l2r [ffun i: 'I_n => fimult (gauss_wt_f i) (f (gauss_pt_f i))].

 Definition integrate_model_r : R :=
    \sum_(i<n) bounded_val (gauss_wt i) * g (gauss_pt i).

Section foo.
Import Reals.
 Definition integrate_model_acc : R := 
 (INR n * eps + INR (2 * n - 1) * eps²) / (1 + eps)² *
(INR n * ((1 + eps / (1 + eps)) * ((2 + eps) * (fb + f_acc)) + eta)) +
((1 + INR n * eps) * INR n * eta +
 INR n *
 (2 * fb * (eps / (1 + eps)) + 2 * (eps * d) * (eps / (1 + eps)) + 2 * (eps * d) +
  2 * f_acc * (eps / (1 + eps)) + 2 * f_acc + fb * eps * (eps / (1 + eps)) + 
  fb * eps + eps * (eps * d) * (eps / (1 + eps)) + eps * (eps * d) +
  eps * f_acc * (eps / (1 + eps)) + eps * f_acc + eta)).
End foo.


Lemma sumB (E1 E2 : 'I_n -> R):
  \sum_(i < n) ( (E2 i) - (E1 i)) =
   (\sum_(i < n) E2 i) - (\sum_(i < n) E1 i).
Proof.
 rewrite bigop.unlock /reducebig.
 induction (index_enum _); simpl.
 lra.
 rewrite {}IHl. lra.
Qed.


 Open Scope R_scope.

Lemma bounded_ext:  forall r x y Hx Hy, x=y -> @Build_bounded r x Hx = @Build_bounded r y Hy.
Proof. intros. subst. f_equal. apply Classical_Prop.proof_irrelevance.
Qed.


Section foo.
 Import Reals.


 Definition model_error1 : R := 2 * fb * (eps / (1 + eps)) + 2 * (eps * d) * (eps / (1 + eps)) + 2 * (eps * d) +
2 * f_acc * (eps / (1 + eps)) + 2 * f_acc + fb * eps * (eps / (1 + eps)) + 
fb * eps + eps * (eps * d) * (eps / (1 + eps)) + eps * (eps * d) +
eps * f_acc * (eps / (1 + eps)) + eps * f_acc + eta.

 Lemma Rabs_le_conversion: forall x y e, Rabs (x-y) <= e -> exists d, Rabs d <= e /\ x = y+d.
 Proof. 
  intros.
  exists (x-y)%R.
  split; try Lra.lra.
Qed.

Lemma Rabs_le_pos: forall  [x y], Rabs x <= y -> 0 <= y.
Proof. intros. transitivity (Rabs x); auto. apply Rabs_pos.
Qed.

Definition maxwf : R := (1 + eps / (1 + eps)) * ((2 + eps) * (fb + f_acc)) + eta.

Lemma RrangeP: forall x y z: R, reflect (x <= y <= z) (x <= y <= z)%Ri.
Proof.
clear.
intros.
pose proof (@RleP x y).
pose proof (@RleP y z).
inversion H; inversion H0.
constructor 1. split; auto.
all: constructor 2; intros [? ?]; contradiction.
Qed.

Lemma maxwf_i': forall i, Rle (Rabs (FS_val (fmult (FIS2FS (gauss_wt_f i)) (FIS2FS (f (gauss_pt_f i)))))) maxwf.
intros.
destruct (fmult_spec (FIS2FS (gauss_wt_f i)) (FIS2FS (f (gauss_pt_f i)))) as [e0 [e1 [He0 _]]].
 rewrite /fmult. rewrite {He0}.
 destruct (frnd_spec  fs (FS_val (FIS2FS (gauss_wt_f i)) * (FIS2FS (f (gauss_pt_f i))))) as [e2 [e3 [He1 _]]].
 rewrite {}He1.
 assert (is_true (-1 <= FS_val (FIS2FS (gauss_pt_f i)) <= 1)%Ri). {
  pose proof (Stdlib.Rabs_def2_le _ _  (gauss_pt_f_range i)).
  clear - H.
  apply /andP. destruct H. split; apply /RleP; auto.
 }
 eapply Rle_trans; [ apply Rabs_triang | ].
 eapply Rle_trans; [ apply Rplus_le_compat ; [ | apply bounded_prop ] | ].
-
 rewrite ?Rabs_mult.
 apply Rmult_le_compat; try apply Rmult_le_pos; try apply Rabs_pos.
 apply Rle_refl.
 apply Rmult_le_compat; try apply Rmult_le_pos; try apply Rabs_pos.
 move :(proj2 (gauss_wts_err i)) => /RleP H1.
 apply Rabs_le_conversion in H1.
  destruct H1 as [d9 [? ?]].
 rewrite {}H1.
 eapply Rle_trans; [ apply Rabs_triang | ].
 eapply Rle_trans; [ apply Rplus_le_compat_l | ]. apply H0.
 apply RIneq.Rle_refl.
 destruct ((fun_acc (gauss_pt_f i))(conj (proj1 (gauss_pts_err i)) H)) as [H0' H0].
 apply Rabs_le_conversion in H0.
 destruct H0 as [d9 [? ?]].
 rewrite {}H1.
 eapply Rle_trans; [ apply Rabs_triang | ].
 eapply Rle_trans; [ apply Rplus_le_compat_l | ]. apply H0.
 apply Rle_refl.
-
 assert (0 <= eps).  move :(proj2 (gauss_pts_err i)) => /RleP H88. eapply Rle_trans. 2: apply H88. apply Rabs_pos.
 assert (0 <= f_acc). 
 move :(fun_acc _ (conj (proj1 (gauss_pts_err i)) H)) =>  H88. eapply Rle_trans; [ | apply H88]. apply Rabs_pos. 
 eapply Rle_trans.
 apply Rplus_le_compat; [ | apply Rle_refl].
 eapply Rle_trans.
 apply Rmult_le_compat; try apply Rmult_le_pos; try apply Rabs_pos.
 eapply Rle_trans; [ | apply Rplus_le_compat; try apply Rabs_pos ].
 rewrite Rplus_0_l. apply H0. apply Rle_refl.
 apply Rplus_le_le_0_compat; auto. apply Rabs_pos.
 eapply Rle_trans. apply Rabs_triang;try apply Rmult_le_pos; try apply Rabs_pos.
 apply Rplus_le_compat. apply Rle_refl. apply bounded_prop.
 apply Rmult_le_compat; try apply Rmult_le_pos; try apply Rabs_pos.
 apply Rplus_le_le_0_compat; try apply Rabs_pos; auto.
 apply Rplus_le_le_0_compat; try apply Rabs_pos; auto.
 apply Rle_trans with (2 + eps). apply Rplus_le_compat.
 apply bounded_prop. apply Rle_refl. apply Rle_refl.
 eapply Rle_trans. apply Rplus_le_compat.
 apply /RleP; apply Hg; auto. apply Rle_refl.
 apply Rle_refl.
 apply Rle_refl.
 rewrite Rabs_R1.
 apply Rle_refl.
Qed.


Lemma gauss_pt_wt_finite: forall i, is_true (finite (fimult (gauss_wt_f i) (f (gauss_pt_f i)))).
Proof.
move => i.
apply fimult_spec_f.
-
apply gauss_wts_err.
-
apply fun_acc.
split.
apply gauss_pts_err.
apply /RrangeP.
apply Rcomplements.Rabs_le_between; auto.
-
eapply Rle_lt_trans.
apply maxwf_i'.
apply /RltP.
move :fb_limit_simple => H.
change (_ + eta)%Ri with maxwf in H.
set x := maxwf in H|-*. clearbody x.
pose proof m_pos FI.
assert (x< 0 \/ x >= 0)%Ri by lra.
change (IZR Z0) with (@Algebra.zero RbaseSymbolsImpl_R__canonical__Algebra_BaseAddUMagma) in H0.
destruct H1.
move :H1 => /RltP H1. apply /RltP.
eapply Rlt_le_trans; eauto.
clear - H H0 H1 i.
destruct (nat_of_ord n).
destruct i; try lia.
replace (S n0) with (1+n0)%nat in H by lia.
rewrite natrD mulrDl in H.
rewrite mul1r in H.
clear i n.
eapply le_lt_trans; [clear H | apply H].
rewrite -{1}(addr0 x).
apply Num.Theory.lerD.
apply /RleP. reflexivity.
apply Num.Theory.mulr_ge0; auto.
Qed.

Lemma maxwf_i: forall i, Rle (Rabs (FS_val (FIS2FS (fimult (gauss_wt_f i) (f (gauss_pt_f i)))))) maxwf.
Proof.
intros.
rewrite fimult_spec; [apply maxwf_i' | apply gauss_pt_wt_finite].
Qed.


Lemma fisum_l2r_finite: forall [n] (h: F ^ n) (b: R),
  (forall i, finite (h i)) ->
  (forall i, Rabs (FIS2FS (h i)) <= b) ->
   ((1%Ri + (n.-1%:R * (eps / (1%Ri + eps)%E))%Ri)%E * (n%:R * b) < m FI)%Ri ->
  finite (fisum_l2r h).
Proof.
intros.
clear - H H0 H1. simpl in *.
destruct n0.
apply finite0.
simpl.
pose h' := [ffun i => h (rshift 1 i)].
rewrite (_: [ffun i => h (lift ord0 i)] = h'); 
  [ | apply eq_dffun => i; rewrite rshift1 //].
assert (forall i, finite (h' i)). move => i. rewrite /h' ffunE //.
assert (forall i, Rabs (FIS2FS (h' i)) <= m FI). {
  move => i; rewrite /h' ffunE //.
  transitivity b0; auto.
  clear - H1.
  simpl in H1.
  set e := (_%:R * _)%Ri in H1.
  assert (0 <= e)%R by admit.
  admit.  (* straightforward *)
}
specialize (H ord0).
specialize (H0 ord0).
clearbody h'.
set c := h ord0 in H,H0|-*.
clearbody c. clear h.
rename h' into h.
Admitted.
(*

assert (H7: Rabs (fsum_l2r_rec (FIS2FS c) [ffun i => FIS2FS (h i)]) <= n0.+1%:R * b0 
             /\ finite (fisum_l2r_rec c h)); [ | apply H7].
pose j := 1%nat.
replace
move :c h H H0 H2 H3; elim n0.
-
move => c h H H0 H2 H3.
simpl; split; auto. rewrite Rmult_1_l //.
-
move => k IH c h H H0 H2 H3.
simpl.
pose h' := [ffun i => h (rshift 1 i)].
rewrite (_: [ffun i => h (lift ord0 i)] = h'); 
  [ | apply eq_dffun => i; rewrite rshift1 //].
destruct (IH (fiplus c (h ord0)) h').


destruct IH.
rewrite (_:  fsum_l2r_rec (fplus (FIS2FS c) ([ffun i => FIS2FS (h i)] ord0))
                       [ffun i => [ffun i0 => FIS2FS (h i0)] (lift ord0 i)]
                = fsum_l2r_rec (FIS2FS (fiplus c (h ord0))) [ffun i => FIS2FS (h' i)]).

replace (k.+2) with (k.+1.+1).
apply IH.

apply IH.
-
rewrite fiplus_spec.
destruct (fplus_spec (FIS2FS c) (FIS2FS (h ord0))) as [d ?].
rewrite {}H4.


*)

Lemma finite_integrate_model: is_true (finite (fisum_l2r [ffun i => fimult (gauss_wt_f i) (f (gauss_pt_f i))])).
Proof.
set h := [ffun _ => _].
assert (forall i, Rle (Rabs (FS_val (FIS2FS (h i)))) maxwf).
  intro i; rewrite /h ffunE; apply maxwf_i.
assert (forall i, finite (h i)).
  intro i; rewrite /h ffunE; apply gauss_pt_wt_finite.
clearbody h.
move :fb_limit H; rewrite /parameter_limits; change (_ + eta)%Ri with maxwf;
  set dd := maxwf  => H1 H.
clearbody dd.
eapply fisum_l2r_finite; eauto.
Qed.

End foo.

Ltac spec H3 := match type of H3 with ?A -> _ => let H := fresh in assert (H: A); [ | specialize (H3 H)] end.


 Lemma integrate_model_err_partial: 
     Rabs (FS_val (FIS2FS integrate_model_f) - integrate_model_r) <= integrate_model_acc. {
Proof.
 intros.
  rewrite /integrate_model_f /integrate_model_r.
 rewrite -fisum_fsum.
2: apply finite_integrate_model.
 rewrite (_:  [ffun i => FIS2FS ([ffun i0 => fimult (gauss_wt_f i0) (f (gauss_pt_f i0))] i)]
               = [ffun i => fmult (FIS2FS (gauss_wt_f i)) (FIS2FS (f (gauss_pt_f i)))]).
2: apply eq_dffun => i; rewrite ffunE; apply FS_val_ext; rewrite  fimult_spec //; apply  gauss_pt_wt_finite.
  move :(@fsum_l2r_reals_err fs n [ffun i: 'I_n => FS_val (fmult (FIS2FS (gauss_wt_f i)) (FIS2FS (f (gauss_pt_f i))))]).
 set ζ := Rdefinitions.Rdiv _ _ . cbv zeta.
 set a := fsum_l2r _. set a' := fsum_l2r _. 
 rewrite (_: a=a'); [  | rewrite {}/a {}/a'; f_equal; apply eq_dffun => x; rewrite ffunE; apply frnd_F].
 clear a. clearbody a'. 
set d8 :=         (\sum_i
            Rabs
              (fun_of_fin
                 [ffun i0 => FS_val (fmult (FIS2FS (gauss_wt_f i0)) (FIS2FS (f (gauss_pt_f i0))))] i)).
assert (Hd8: d8 <= Raxioms.INR n * maxwf). {
 rewrite /d8.
 apply /RleP.
 eapply RIneq.Rle_trans. apply (@Rle_big_compat  _ _ (fun=> maxwf)).
 intros. rewrite ffunE. apply maxwf_i'.
  rewrite big_sum_const.
 apply RIneq.Rle_refl. 
}
clearbody d8.
assert (Rabs (\sum_(i < n) bounded_val (gauss_wt i) * g (gauss_pt i) 
               - \sum_(i < n) FS_val (fmult (FIS2FS (gauss_wt_f i)) (FIS2FS (f (gauss_pt_f i)))))
      <= Raxioms.INR n * model_error1). {
 clear ζ.
 rewrite -sumB.
 eapply le_trans. apply /RleP. apply big_Rabs_triang.
 eapply le_trans. apply /RleP. apply (@Rle_big_compat  _ _ (fun=> model_error1)).
 2: rewrite big_sum_const //.
 move => i.
 move :(gauss_pts_err i) => Hpt.
 move :(gauss_wts_err i) => Hwt.
 destruct (fmult_spec (FIS2FS (gauss_wt_f i)) (FIS2FS (f (gauss_pt_f i)))) as [e0 [e1 [He0 _]]].
 rewrite /fmult. rewrite {He0}.
 destruct (frnd_spec  fs (FS_val (FIS2FS (gauss_wt_f i)) * (FIS2FS (f (gauss_pt_f i))))) as [e2 [e3 [He1 _]]].
 rewrite {}He1.
 Import Reals. 
 assert (is_true (-1 <= FS_val (FIS2FS (gauss_pt_f i)) <= 1)%Ri). {
  pose proof (Stdlib.Rabs_def2_le _ _  (gauss_pt_f_range i)).
  clear - H.
  apply /andP. destruct H. split; apply /RleP; auto.
 }  
 move :(fun_acc (gauss_pt_f i) (conj (proj1 Hpt) H)) => Hf.
 repeat change (@GRing.add _) with Rplus in *.
 repeat change (@GRing.mul _) with Rmult in *.
 repeat change (@GRing.opp _)  with Ropp in *.
 repeat change (@Algebra.opp _)  with Ropp in *.
set j := bounded_val _.
set k := bounded_val _.
set j' := FS_val _.
set k' := FS_val _.
set e7 := bounded_val _.
set e8 := bounded_val _.
 replace (_ + - _) with ( j* g k - j' * k' -e7 * (j' * k') - e8) by ring. 
 subst j k j' k'.
 destruct Hpt as [_ Hpt]. destruct Hwt as [_ Hwt].
 move :Hpt => /RleP Hpt.
 move :Hwt => /RleP Hwt.
 apply Rabs_le_conversion in Hpt, Hwt.
 destruct Hpt as [e9 [? ?]].
 destruct Hwt as [e10 [? ?]].
 rewrite H3. 
 destruct Hf as [_ Hf].
 apply Rabs_le_conversion in Hf.
 destruct Hf as [e11 [He11 Hf]].
 rewrite Hf in H|-*.
 rewrite H1 in H|-*.
 pose proof (g_max_deriv (gauss_pt i) e9).
 spec H4. apply /RrangeP. apply Raux.Rabs_le_inv.  apply bounded_prop. 
 spec H4. apply /RrangeP. apply Raux.Rabs_le_inv. eapply Rle_trans. apply H0.
    apply Rlt_le. apply eps_lt_1.
move :H4 => /RleP H4.
 repeat change (@GRing.add _) with Rplus in *.
 repeat change (@GRing.mul _) with Rmult in *.
 repeat change (@GRing.opp _)  with Ropp in *.
 repeat change (@Algebra.opp _)  with Ropp in *.
try change (@Algebra.natmul _  _ _) with 2%R in *.
apply Rabs_le_conversion in H4.
destruct H4 as [e12 [He12 He12']].
rewrite {}He12'.
 repeat change (@GRing.mul _) with Rmult in *.
pose proof (bounded_prop (gauss_pt i)).
set  p := bounded_val (gauss_pt i) in H4|-*.
pose proof (bounded_prop (gauss_wt i)).
set w := bounded_val (gauss_wt i) in H7|-*.
try change (@Algebra.natmul _  _ _) with 2%R in *.
pose proof (Hg p). 
 spec H8. apply /RrangeP. apply Raux.Rabs_le_inv.  apply bounded_prop. 
move :H8 => /RleP H8.
clearbody p. clearbody w.
assert (H18: 0 <= d). {
 clear - Hd. specialize (Hd 0).
 etransitivity. 2: apply /RleP. 2:  apply Hd. rewrite -RabsE. apply Rabs_pos.
 apply /RrangeP. 
 clear. change (@Algebra.opp _) with Ropp.
 change (@GRing.one _) with R1. Lra.lra.
}
pose proof (bounded_prop e2).  fold e7 in H10. clearbody e7.
pose proof (bounded_prop e3). fold e8 in H11. clearbody e8.
clear - H10 H11 H8 H9 H7 H4 He12 H2 H0 He11 H18.
pose proof (Rabs_le_pos H8).
pose proof (Rabs_le_pos H0).
pose proof (Rabs_le_pos H11).
match goal with |- Rabs ?A <= _ => ring_simplify A end.
assert (Rabs e12 <= eps * d). {
 etransitivity. eassumption.  apply Rmult_le_compat_r; auto.
} 
clear He12.
repeat match goal with
 | |- Rabs _ <= _ => eassumption
 | |- Rabs (- _) <= _ => rewrite Rabs_Ropp
 |  |- Rabs (_ + _) <=  _ => etransitivity; [ apply Rabs_triang | ]
 |  |- Rabs (_ - _) <=  _ => etransitivity; [ apply Rabs_triang | ]
 | |- Rabs _ + Rabs _ <= _ => etransitivity; [apply Rplus_le_compat |  ]
 | |- Rabs (_ * _) <= _ => rewrite ?Rabs_mult
 | |-  _ * _ <= _ => apply Rmult_le_compat
 | |- 0 <= _ * _ => apply Rmult_le_pos
 | |- 0 <= Rabs _ => apply Rabs_pos
 | |- _ => apply Rle_refl
 end.
}
intro.
set j := \sum_(i < n) bounded_val (gauss_wt i) * g (gauss_pt i) in H |- *.
clearbody j.
set k := \sum_(i < nat_of_ord n) FS_val (fmult (FIS2FS (gauss_wt_f i)) (FIS2FS (f (gauss_pt_f i)))) in H.
set k' := (\sum__ _) in fsum_l2r_reals_err.
assert (k = k'). apply eq_big; auto => i _. rewrite ffunE //.
clearbody k'. subst k'. clearbody k.
apply /RleP.
move :H => /RleP H.
transitivity (Rabs (k - FS_val a') + Rabs (j-k)).
 repeat change (@GRing.add _) with Rplus in *.
 repeat change (@GRing.mul _) with Rmult in *.
 repeat change (@GRing.opp _)  with Ropp in *.
 repeat change (@Algebra.opp _)  with Ropp in *.
replace (FS_val a' + - j) with (FS_val a' - k + (k - j)) by Lra.lra.
etransitivity; [ apply Rabs_triang | ].
apply Rplus_le_compat;
rewrite Rabs_minus_sym; apply Rle_refl.
eapply Rle_trans.
apply Rplus_le_compat; try eassumption.
rewrite ?Rplus_assoc.
eapply Rle_trans.
apply Rplus_le_compat_r.
apply Rmult_le_compat_l.
2: apply /RleP; apply Hd8.
rewrite /ζ.
apply Rcomplements.Rdiv_le_0_compat.
apply Rplus_le_le_0_compat.
apply Rmult_le_pos.  apply pos_INR. auto. apply eps_pos.
apply Rmult_le_pos. apply pos_INR. apply Rle_0_sqr.
apply Rsqr_pos_lt.
pose proof eps_pos fs. clear - H0. Lra.lra.
apply Rle_refl.
}
Qed.

 Lemma integrate_model_err: 
     Rabs (FS_val (FIS2FS integrate_model_f) - ∫ g) <= integrate_model_acc + b. {
Proof.
 intros.
 replace (FS_val (FIS2FS integrate_model_f) - ∫ g) with
    (FS_val (FIS2FS integrate_model_f) - integrate_model_r + (integrate_model_r - ∫ g))
  by Lra.lra.
 etransitivity; [apply Rabs_triang | ].
 apply Rplus_le_compat.
 apply /RleP.
 apply integrate_model_err_partial.
 apply quadrature_error_bound_is_bound in Hb.
 rewrite Rabs_minus_sym.
 replace integrate_model_r with (Gauss_Legendre_quadrature n g). 2:{
   rewrite /Gauss_Legendre_quadrature /integrate_model_r /compute_G.
   apply eq_big => i; auto. move => _.
   rewrite /gauss_wt /gauss_pt /bounded_val.
   rewrite /quadrature2.gauss_wt /quadrature2.gauss_pt.
   f_equal. f_equal.
   f_equal. f_equal. f_equal.
   clear.
   ord_enum_cases n; reflexivity.
 }
 rewrite RabsE.
 apply /RleP. apply Hb.
}
Qed.


End FLOAT.


