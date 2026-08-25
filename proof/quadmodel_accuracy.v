
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

(*From Stdlib Require Import Reals Psatz.
From Flocq Require Import Core.Raux.

From libValidSDP Require Import misc fsum fsum_l2r.

From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat.
From mathcomp Require Import fintype finfun ssralg bigop eqtype seq path.
From mathcomp Require Import Rstruct.

From CFEM Require Import quadrature quadrature2. Import Legendre.
Import mathcomp.algebra.num_theory.numdomain.Num.

Local Notation R := (RbaseSymbolsImpl_R__canonical__reals_Real).

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

*)
Require Import Lia.

From libValidSDP Require Import misc fsum fsum_l2r.
Import Rbasic_fun.
Import Rstruct.

Open Scope R_scope.
Open Scope ring_scope.

Delimit Scope ring_scope with Ri.
Delimit Scope R_scope with Re.

Local Notation R := (RbaseSymbolsImpl_R__canonical__reals_Real).

Import Interval.Tactic.

Section FLOAT.
 
 Variable fs: Float_spec.

Notation F := (FS fs).
Notation frnd := (frnd fs).
Notation eps := (eps fs).
Notation eta := (eta fs).
Variable n: 'I_5.

 Variable gauss_pt_f: forall (i: 'I_n), F.
 Variable gauss_wt_f: forall (i: 'I_n), F.
 Variable gauss_pt_f_range: forall i, Rdefinitions.Rle (Rabs (gauss_pt_f i)) 1.

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
 
 Variable gauss_pts_err: forall (i: 'I_n),  Rabs (FS_val (gauss_pt_f i) - bounded_val (gauss_pt i)) <= eps.
 Variable gauss_wts_err: forall (i: 'I_n),  Rabs (FS_val (gauss_wt_f i) - bounded_val (gauss_wt i)) <= eps.

 Variable (fb: R).
 Variable(g: R -> R).
 Variable Hg: forall x, -1 <= x <= 1 -> Rabs (g x) <= fb.
 Variable (b: R) (Hb: quadrature_error_bound g n b).
 Variable (d: R) (Hd: deriv_bound g d).


  Lemma g_max_deriv: forall x y, -1 <= x <= 1 -> -1 <= y <= 1 -> Rabs (g(x+y) - g x) <= Rabs y * d.
 Admitted.

 Variable (f: F -> F)  (f_acc: R).
 Variable (fun_acc: forall (x: F), -1 <= FS_val x <= 1 -> 
                         Rdefinitions.Rle (Rabs (FS_val (f x) - g (FS_val x))) f_acc).
  

 Definition integrate_model_f  : F :=
     fsum_l2r [ffun i: 'I_n => fmult (gauss_wt_f i) (f (gauss_pt_f i))].

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

From libValidSDP Require Import fcmsum.


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

Lemma maxwf_i: forall i, Rle (Rabs (FS_val (fmult (gauss_wt_f i) (f (gauss_pt_f i))))) maxwf.
intros.
 destruct (fmult_spec (gauss_wt_f i) (f (gauss_pt_f i))) as [e0 [e1 [He0 _]]].
 rewrite /fmult. rewrite {He0}.
 destruct (frnd_spec  fs (FS_val (gauss_wt_f i) * f (gauss_pt_f i))) as [e2 [e3 [He1 _]]].
 rewrite {}He1.
 assert (is_true (-1 <= FS_val (gauss_pt_f i) <= 1)%Ri). {
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
 move :(gauss_wts_err i) => /RleP H1.
 apply Rabs_le_conversion in H1.
  destruct H1 as [d9 [? ?]].
 rewrite {}H1.
 eapply Rle_trans; [ apply Rabs_triang | ].
 eapply Rle_trans; [ apply Rplus_le_compat_l | ]. apply H0.
 apply RIneq.Rle_refl.
 pose proof (fun_acc (gauss_pt_f i)) H.
 apply Rabs_le_conversion in H0.
 destruct H0 as [d9 [? ?]].
 rewrite {}H1.
 eapply Rle_trans; [ apply Rabs_triang | ].
 eapply Rle_trans; [ apply Rplus_le_compat_l | ]. apply H0.
 apply Rle_refl.
-
 assert (0 <= eps).  move :(gauss_pts_err i) => /RleP H88. eapply Rle_trans. 2: apply H88. apply Rabs_pos.
 assert (0 <= f_acc). 
 move :(fun_acc _ H) =>  H88. eapply Rle_trans; [ | apply H88]. apply Rabs_pos. 
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

End foo.

Ltac spec H3 := match type of H3 with ?A -> _ => let H := fresh in assert (H: A); [ | specialize (H3 H)] end.

 Lemma integrate_model_err: 
     Rabs (FS_val integrate_model_f - integrate_model_r) <= integrate_model_acc. {
Proof.
 intros.
  rewrite /integrate_model_f /integrate_model_r.
  move :(@fsum_l2r_reals_err fs n [ffun i: 'I_n => FS_val (fmult (gauss_wt_f i) (f (gauss_pt_f i)))]).
 set ζ := Rdefinitions.Rdiv _ _ . cbv zeta.
 set a := fsum_l2r _. set a' := fsum_l2r _. 
 rewrite (_: a=a'); [  | rewrite {}/a {}/a'; f_equal; apply eq_dffun => x; rewrite ffunE; apply frnd_F].
 clear a. clearbody a'. 
set d8 :=         (\sum_i
            Rabs
              (fun_of_fin
                 [ffun i0 => FS_val (fmult (gauss_wt_f i0) (f (gauss_pt_f i0)))] i)).
assert (Hd8: d8 <= Raxioms.INR n * maxwf). {
 rewrite /d8.
 apply /RleP.
 eapply RIneq.Rle_trans. apply (@Rle_big_compat  _ _ (fun=> maxwf)).
 intros. rewrite ffunE. apply maxwf_i.
  rewrite big_sum_const.
 apply RIneq.Rle_refl. 
}
clearbody d8.
assert (Rabs (\sum_(i < n) bounded_val (gauss_wt i) * g (gauss_pt i) - \sum_(i < n) FS_val (fmult (gauss_wt_f i) (f (gauss_pt_f i))))
      <= Raxioms.INR n * model_error1). {
 clear ζ.
 rewrite -sumB.
 eapply le_trans. apply /RleP. apply big_Rabs_triang.
 eapply le_trans. apply /RleP. apply (@Rle_big_compat  _ _ (fun=> model_error1)).
 2: rewrite big_sum_const //.
 move => i.
 move :(gauss_pts_err i) => Hpt.
 move :(gauss_wts_err i) => Hwt.
 destruct (fmult_spec (gauss_wt_f i) (f (gauss_pt_f i))) as [e0 [e1 [He0 _]]].
 rewrite /fmult. rewrite {He0}.
 destruct (frnd_spec  fs (FS_val (gauss_wt_f i) * f (gauss_pt_f i))) as [e2 [e3 [He1 _]]].
 rewrite {}He1.
 Import Reals. 
 assert (is_true (-1 <= FS_val (gauss_pt_f i) <= 1)%Ri). {
  pose proof (Stdlib.Rabs_def2_le _ _  (gauss_pt_f_range i)).
  clear - H.
  apply /andP. destruct H. split; apply /RleP; auto.
 }  
 move :(fun_acc (gauss_pt_f i) H) => Hf.
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
 move :Hpt => /RleP Hpt.
 move :Hwt => /RleP Hwt.
 apply Rabs_le_conversion in Hpt, Hwt.
 destruct Hpt as [e9 [? ?]].
 destruct Hwt as [e10 [? ?]].
 rewrite H3. 
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
change (@Algebra.natmul _  _ _) with 2%R in *.
apply Rabs_le_conversion in H4.
destruct H4 as [e12 [He12 He12']].
rewrite {}He12'.
 repeat change (@GRing.mul _) with Rmult in *.
pose proof (bounded_prop (gauss_pt i)).
set  p := bounded_val (gauss_pt i) in H4|-*.
pose proof (bounded_prop (gauss_wt i)).
set w := bounded_val (gauss_wt i) in H7|-*.
change (@Algebra.natmul _  _ _) with 2%R in *.
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
set k := \sum_(i < nat_of_ord n) FS_val (fmult (gauss_wt_f i) (f (gauss_pt_f i))) in H.
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

End FLOAT.


