From LAProof Require Import preamble common sum_model sum_is_finite dotprod_model 
    float_acc_lems dot_acc gemv_acc mv_mathcomp sum_acc.
From CFEM Require Import quadrature quadrature2. Import Legendre.

Import Interval.Tactic.

From Stdlib Require Import ProofIrrelevance.


Open Scope R_scope.

Lemma BMULT_correct :
  forall  {NAN : FPCore.Nans} {t : type} (x y : ftype t)
    (FINx: Binary.is_finite x = true)
    (FINy: Binary.is_finite y = true)
    (FIN : @Bmult_no_overflow t (FT2R x) (FT2R y)),
  Binary.is_finite (BMULT x y) = true /\
  exists delta, exists epsilon,
    delta * epsilon = 0 /\
    Rabs delta <= @default_rel t /\
    Rabs epsilon <= @default_abs t /\
    (FT2R (BMULT x y) = (FT2R x * FT2R y) * (1 + delta) + epsilon).
Proof.
  intros.
  pose proof (Binary.Bmult_correct (fprec t) (femax t) (fprec_gt_0 t) (fprec_lt_femax t)
                (FPCore.mult_nan (fprec t) (femax t) (fprec_gt_one t))
                BinarySingleNaN.mode_NE x y).
  cbv zeta in H.
  pose proof (
    Raux.Rlt_bool_spec
      (Rabs
         (Generic_fmt.round Zaux.radix2
            (SpecFloat.fexp (fprec t) (femax t))
            (BinarySingleNaN.round_mode BinarySingleNaN.mode_NE)
            (Binary.B2R _ _ x * Binary.B2R _ _ y))) (@fmax t)).
  fold (@FT2R t) in H, H0.
  unfold fmax in *.
  destruct H0.
  - destruct H as [? [? _]].
    split.  rewrite FINx  in H1.  rewrite FINy in H1. apply H1.
    unfold BMULT, BINOP.
    rewrite {}H.
    apply generic_round_property.
  - red in FIN. unfold rounded in FIN.
    unfold fmax in *.
    lra.
Qed.

 Lemma Rabs_le_conversion: forall x y e, Rabs (x-y) <= e -> exists d, Rabs d <= e /\ x = y+d.
 Proof. 
  intros.
  exists (x-y).
  split; lra.
Qed.

Lemma Rabs_le_pos: forall  [x y], Rabs x <= y -> 0 <= y.
Proof. intros. transitivity (Rabs x); auto. apply Rabs_pos.
Qed.

Lemma RrangeP: forall x y z: R, reflect (x <= y <= z) (x <= y <= z)%O.
Proof.
clear.
intros.
pose proof (@RleP x y).
pose proof (@RleP y z).
inversion H; inversion H0.
constructor 1. split; auto.
all: constructor 2; intros [? ?]; contradiction.
Qed.

Section FLOAT.

 Variable t: type.
 Variable nan: FPCore.Nans.
 Notation F := (ftype t).

Notation eps := (@default_rel t).
Notation eta := (@default_abs t).

 Variable n: 'I_5.

 Variable gauss_pt_f: forall (i: 'I_n), F.
 Variable gauss_wt_f: forall (i: 'I_n), F.

 Variable gauss_pt_f_range: forall i, Rabs (FT2R (gauss_pt_f i)) <= 1.

 Lemma gauss_pt_range: forall i, Rabs (gauss_pt n i) <= 1.
 Proof.
 intros. pose proof (gauss_pt_range n i).
 prepare_for_interval.
 apply Rabs_le; auto.
Qed. 

 Lemma gauss_wt_range: forall i, Rabs (gauss_wt n i) <= 2.
 Proof.
 intros. pose proof (gauss_wt_range n i).
 prepare_for_interval.  set a := gauss_wt _ _ in H|-*. clearbody a.
 apply Rabs_le; auto. simpl in H. lra.
Qed.

 Local Definition finite {t} (x: ftype t) := is_true (Binary.is_finite x).

 Definition gauss_pts_accuracy := forall (i: 'I_n),  finite (gauss_pt_f i) /\ Rabs (FT2R (gauss_pt_f i) - gauss_pt n i) <= eps.

 Variable gauss_pts_err: gauss_pts_accuracy.

 Definition gauss_wts_accuracy := forall (i: 'I_n), finite (gauss_wt_f i) /\  Rabs (FT2R (gauss_wt_f i) - gauss_wt n i) <= eps.
 Variable gauss_wts_err: gauss_wts_accuracy.

 Variable (fb: R).
 Variable(g: R -> R).

  Definition fbound g fb := forall x : R, -1 <= x <= 1 -> Rabs (g x) <= fb.
 Variable Hg: fbound g fb.

 Variable (b: R) (Hb: quadrature_error_bound g n b).
 Variable (d: R) (Hd: deriv_bound g d).

  Lemma g_max_deriv: forall x y, -1 <= x <= 1 -> -1 <= x+y <= 1 -> Rabs (g(x+y) - g x) <= Rabs y * d.
 Admitted.

 Variable (f: F -> F)  (f_acc: R).

 Definition function_accuracy := forall (x: F), finite x /\ -1 <= FT2R x <= 1 -> 
             finite (f x) /\  Rabs (FT2R (f x) - g (FT2R x)) <= f_acc.
 Variable fun_acc: function_accuracy.

 Definition parameter_limits : Prop := 
   (1 + n.-1%:R * (eps / (1 + eps))) * 
     (n%:R * ((1 + eps / (1 + eps)) * ((2 + eps) * (fb + f_acc)) + eta)) <    bpow Zaux.radix2 (femax t).

 Variable fb_limit:  parameter_limits. 

 Lemma fb_limit_simple: 
     (n%:R * ((1 + eps / (1 + eps)) * ((2 + eps) * (fb + f_acc)) + eta)) <   bpow Zaux.radix2 (femax t).
 Proof.
  have :(1 <=  (1 + n.-1%:R * (eps / (1 + eps))) ).
  transitivity (1 + 0). lra. apply Rplus_le_compat. reflexivity.
 apply Rmult_le_pos. apply /RleP. apply ler0n.
 apply Stdlib.Rdiv_pos_compat.
 apply default_rel_ge_0.
 apply default_rel_plus_1_gt_0.
 move => H.
 eapply Rle_lt_trans; [ | apply fb_limit].
 set a := 1 + _ in H. fold a. clearbody a.
 set e := _ * _.
 assert (0 <= e). {
    apply Rmult_le_pos. apply /RleP; apply ler0n.
   apply Rplus_le_le_0_compat; [ | apply default_abs_ge_0].
    repeat apply Rmult_le_pos. 
  apply Rplus_le_le_0_compat; try lra.
 apply Stdlib.Rdiv_pos_compat.
 apply default_rel_ge_0.
 apply default_rel_plus_1_gt_0.
  apply Rplus_le_le_0_compat; try lra.
 apply default_rel_ge_0.
  apply Rplus_le_le_0_compat; try lra.
  specialize (Hg 0 ltac:(lra)). etransitivity; [ | apply Hg]. apply Rabs_pos.
 destruct (fun_acc (Zconst t 0)). split; auto. reflexivity. simpl. lra.
  etransitivity; [ | apply H1]. apply Rabs_pos.
}
 transitivity (1*e). lra.
 apply Rmult_le_compat_r; auto.
Qed.

 Definition integrate_model_f  : F :=
    dotprodF (map gauss_wt_f (ord_enum n)) (map (comp f (gauss_pt_f)) (ord_enum n)).

 Definition integrate_model_r : R :=
    \sum_(i<n)  (gauss_wt n i) * g (gauss_pt n i).

Definition maxwf : R := 
    fb * eps ^ 2 + 3 * fb * eps + eps ^ 3 * d + 3 * eps ^ 2 * d +
    eps ^ 2 * f_acc + 2 * eps * d + 3 * eps * f_acc + 2 * f_acc + eta.

 Definition integrate_model_acc : R := 
  (((1 + eps) ^ n - 1) * (INR n * (2 * fb + maxwf)) + INR n * maxwf).

Lemma sumB (E1 E2 : 'I_n -> R):
  \sum_(i < n) ( (E2 i) - (E1 i)) =
   (\sum_(i < n) E2 i) - (\sum_(i < n) E1 i).
Proof.
 rewrite bigop.unlock /reducebig.
 induction (index_enum _); simpl.
 prepare_for_interval; simpl; auto.
 rewrite {}IHl. set c := foldr _ _ _. set c' := foldr _ _ _. clearbody c. clearbody c'.
 clear. prepare_for_interval; lra.
Qed.

Definition gauss_wt_f_range := forall i, 0 <= FT2R (gauss_wt_f i) <= 2.

Variable gauss_wt_f_range_ok: gauss_wt_f_range.

Lemma gauss_pt_wt_limit_aux: 2 * (fb + f_acc) * (1 + eps) + eta < @fmax t.
Admitted. (* should be fine *)

Ltac all_bounded e :=
 lazymatch e with
 | ?a + ?b => all_bounded a; all_bounded b
 | ?a * ?b => all_bounded a; all_bounded b
 | _ => lazymatch goal with H: Rabs e <= _ |- _ => try clearbody e | _ => 
                fail "This subterm does not have a bound above the line (of the form H: Rabs _ <= _):" e
            end
 end.

Ltac bound_sum_of_products := 
match goal with |- Rabs ?e <= _ => all_bounded e end;
repeat (eapply Rle_trans; [ apply Rabs_triang | eapply Rle_trans; [apply Rplus_le_compat | ]]);
 try lazymatch goal with |- _ + _ <= ?C => is_evar C; apply Rle_refl end;
 rewrite ?Rabs_mult; repeat apply Rmult_le_compat;
 repeat apply Rmult_le_pos;
 try apply Rabs_pos;
 try eassumption.

(* TODO:  quadrature2.gauss_{pt,wt} should have n argument implicit *)
Lemma gauss_pt_wt_acc: forall i,
    finite (BMULT (gauss_wt_f i) (f (gauss_pt_f i))) /\
    Rabs (FT2R (BMULT (gauss_wt_f i) (f (gauss_pt_f i))) - gauss_wt n i * (g (gauss_pt n i))) <= maxwf.
Proof.
move => i.
destruct (fun_acc (gauss_pt_f i)) as [FINf Hacc].
  split; [apply gauss_pts_err | apply Rabs_le_inv;  apply gauss_pt_f_range].
assert (Hfb := gauss_pt_f_range i).
assert (Hgb := Hg (FT2R (gauss_pt_f i)) (Rabs_le_inv _ _ Hfb)).
assert (Hwb := gauss_wt_f_range_ok i).
assert (Rabs (FT2R (f (gauss_pt_f i))) <= fb + f_acc). {
  replace (FT2R (f (gauss_pt_f i))) with (g (FT2R (gauss_pt_f i)) + (FT2R (f (gauss_pt_f i)) - g (FT2R (gauss_pt_f i))))
    by lra.
 etransitivity; [apply Rabs_triang  | ].
 lra.
}
destruct (BMULT_correct (gauss_wt_f i) (f (gauss_pt_f i))) as [FIN [e0 [e1 [_ [He0 [He1 He01]]]]]]; auto;
 try apply gauss_wts_err.   {
 red. 
 destruct (@generic_round_property t (FT2R (gauss_wt_f i) * FT2R (f (gauss_pt_f i))))
      as [e2 [e3 [_ [He2 [He3 He23]]]]].
 unfold rounded. rewrite {}He23.
 eapply Rle_lt_trans; [ apply Rabs_triang | ].
 rewrite ?Rabs_mult.
 apply Rle_lt_trans with (2 * (fb + f_acc) * (1+eps) + eta).
 - apply Rplus_le_compat; auto.
  apply Rmult_le_compat; auto; try (rewrite -?Rabs_mult; apply Rabs_pos).
  apply Rmult_le_compat; auto; try apply Rabs_pos.
 apply Rabs_le. lra.
 eapply Rle_trans; [ apply Rabs_triang | ].
 rewrite Rabs_R1. lra.
- apply gauss_pt_wt_limit_aux. 
}
 split; auto. clear FIN.
 rewrite {}He01.
 destruct (gauss_wts_err i) as [FIN3 H3].
 set e3 := FT2R (gauss_wt_f i) - gauss_wt n i in H3.
 destruct (gauss_pts_err i) as [FIN4 H4].
 set e4 := FT2R (gauss_pt_f i) - gauss_pt n i in H4.
 replace (FT2R (gauss_pt_f i)) with (gauss_pt n i + e4) in Hacc by (rewrite /e4; lra).
 assert (Hdpos: 0 <= d). {
    pose proof Hd 0. set c := _ g _ in H0. change (numdomain.Num.norm ?A) with (Rabs A) in H0.
   transitivity (Rabs c). apply Rabs_pos. apply /RleP. apply H0. apply /RrangeP. 
   clear; prepare_for_interval; simpl; lra.
 }
assert (Hderiv: Rabs (g (gauss_pt n i + e4) - g (gauss_pt n i)) <= eps * d). {
  assert ( -1 <= gauss_pt n i + e4 <= 1 ). {
   replace (gauss_pt n i + e4) with (FT2R (gauss_pt_f i)) by (rewrite /e4; lra).
    apply Rabs_le_inv. apply gauss_pt_f_range.
 }
 move :(g_max_deriv (gauss_pt n i) e4 (Rabs_le_inv _ _ (gauss_pt_range i)) H0) => H1; clear H0.
 etransitivity. apply H1. apply Rmult_le_compat_r; auto.
}
set e5 := _ - _ in Hderiv.
set e6 := _ - _ in Hacc.
replace (FT2R (f (gauss_pt_f i))) with (g (gauss_pt n i) + e5 + e6) by (rewrite /e5 /e6; lra).
replace (FT2R (gauss_wt_f i)) with (gauss_wt n i + e3) by (rewrite /e3; lra).
match goal with |- Rabs ?A <= _ =>   ring_simplify A end.
 assert (Rabs (g (gauss_pt n i)) <= fb). {
   apply Hg. apply Rabs_le_inv. apply gauss_pt_range.
}
 assert (Rabs (gauss_wt n i) <= 2). {
    apply gauss_wt_range.
}
 bound_sum_of_products.
 match goal with |- ?A <= _ => ring_simplify A end.
 reflexivity.
Qed.


Lemma gauss_pt_wt_bound: forall i,
    Rabs (FT2R (BMULT (gauss_wt_f i) (f (gauss_pt_f i)))) <= 2 * fb + maxwf.
Proof.
move => i.
destruct (gauss_pt_wt_acc i).
set a := FT2R _ in H0|-*.
apply Rabs_le_minus in H0.
rewrite Rplus_comm.
etransitivity. apply H0.
apply Rplus_le_compat_l.
assert (Rabs (g (gauss_pt n i)) <= fb).
  by (apply Hg; apply Rabs_le_inv; apply gauss_pt_range).
pose proof (gauss_wt_range) i.
bound_sum_of_products.
Qed.

Lemma rev_list_rev: @rev = @List.rev.
Admitted.

Lemma Forall2_forall:
  forall [A B: Type] (P: A -> B -> Prop) (al: list A) (bl: list B),
    Forall2 P al bl <-> (forall a b, In (a,b) (zip al bl) -> P a b).
Admitted.

Definition dotprodF' (v1 v2 : List.list (ftype t)) : ftype t :=
  dotprod_model.dotprod BMULT BPLUS neg_zero v1 v2.


Lemma dotprodF_dotprodF'_feq: forall al bl, feq (dotprodF al bl) (dotprodF' al bl).
Proof.
rewrite /dotprodF /dotprodF' /dotprod_model.dotprod /=.
set c := pos_zero.
set c' := neg_zero.
assert (feq c c') by reflexivity.
clearbody c'. clearbody c.
intro al.
revert c c' H; induction al; destruct bl; simpl; auto.
apply IHal.
apply BPLUS_mor.
reflexivity.
auto.
Qed.

Lemma dotprodF_dotprodF'_finite: forall al bl, 
   Binary.is_finite (dotprodF al bl) = Binary.is_finite (dotprodF' al bl).
Proof.
intros.
apply is_finite_mor.
apply dotprodF_dotprodF'_feq.
Qed.


Lemma finite_integrate_model_aux: 
  2 * fb + maxwf <
  @fmax t / (1 + eps) * 1 /
  (1 + INR (nat_of_ord n) * (@common.g t (nat_of_ord n - 1) + 1)).
Admitted.

Lemma Fsum_gauss_wt_pt_finite: 
   finite (F.sum (fun i => BMULT (gauss_wt_f i) (f (gauss_pt_f i)))).
Proof.
  apply (finite_sum_from_bounded _ _ (rev (map (fun i => BMULT (gauss_wt_f i) (f (gauss_pt_f i))) (ord_enum n)))).
  - red. set a := (fun _ => _). clearbody a.
     rewrite F.sum_sumF /sumF.
    set z := neg_zero. clearbody z.
  rewrite -{2}(revK (map _ _)).
  rewrite foldl_rev.
  set dl := rev (map _ _). clearbody dl. clear - z dl.
  revert z; induction dl; simpl; intros. constructor.
  rewrite {1}/Basics.flip. simpl. constructor. apply IHdl.
- intros.
 rewrite rev_list_rev -In_rev in_map_iff in H.
 destruct H as [y [? ?]]. subst x.
 rewrite rev_list_rev length_rev length_map (erefl: @length = @size) size_ord_enum.
 split.
 apply gauss_pt_wt_acc.
eapply Rle_lt_trans.
apply gauss_pt_wt_bound.
rewrite /fun_bnd /=.
apply finite_integrate_model_aux.
Qed.

Lemma dotprodF_finite_from_bounded: 
 forall (al bl: list (ftype t)),
   Forall2 (fun x y => finite (BMULT x y) /\ Rabs (FT2R (BMULT x y)) < fun_bnd t (length al)) al bl ->
   finite (dotprodF al bl).
Proof.
intros.
red.
rewrite dotprodF_dotprodF'_feq.
apply (finite_sum_from_bounded _ _ (rev (map (uncurry BMULT) (zip al bl))) (dotprodF' al bl)). {
  red.
  rewrite /dotprodF' /dotprod_model.dotprod /=.
  set c := neg_zero. clearbody c.
  rewrite -{2}(revK (map _ _)).
  rewrite foldl_rev.
  set dl := rev _. clearbody dl. clear - c dl.
  revert c; induction dl; simpl; intros. constructor.
  rewrite {1}/Basics.flip. constructor. apply IHdl.
}
intros.
 move :(Forall2_length H) => EQ.
 rewrite rev_list_rev in H0. rewrite -In_rev in H0.
 rewrite in_map_iff in H0.
 destruct H0 as [[a' b'] [? ?]].
 rewrite Forall2_forall in H. apply H in H1. subst x.
 destruct H1; split; auto.
 rewrite rev_list_rev length_rev length_map (erefl: @length = @size) size_zip.
 rewrite (erefl: @size = @length)  -EQ /minn ltnn /uncurry //.
Qed.


Lemma finite_integrate_model: finite integrate_model_f.
Proof.
rewrite /integrate_model_f.
apply dotprodF_finite_from_bounded.
apply Forall2_forall.
intros.
rewrite zip_map in H.
rewrite in_map_iff in H. destruct H as [i [? ?]].
inversion H; clear H; subst a b0.
rewrite ?ffunE.
rewrite length_map.
rewrite (erefl: @length = @size) size_ord_enum.
split.
apply (gauss_pt_wt_acc i).
eapply Rle_lt_trans.
apply gauss_pt_wt_bound.
rewrite /fun_bnd /=.
apply finite_integrate_model_aux.
Qed.

Lemma integrate_model_r_eq: 
  integrate_model_r = 
    dotprodR  (map (gauss_wt n) (ord_enum n))
               (map (comp g (gauss_pt n)) (ord_enum n)).
Proof.
clear.
rewrite /integrate_model_r.
set a := gauss_wt n.
change (fun i  =>  _)
   with (fun i => BigBody i Algebra.add true (a i * (comp g (gauss_pt n) i))).
 set b := _ \o _.
clearbody a. clearbody b.
rewrite /dotprodR /dotprod_model.dotprod.
rewrite foldl_foldr.
2: rewrite /Basics.flip; intros x y z; lra.
2: rewrite /Basics.flip; intros x y; lra.
rewrite zip_map.
rewrite -map_comp /comp /uncurry.
rewrite bigop.unlock /reducebig.
rewrite index_ord_enum.
change GRing.mul with Rmult.
rewrite /comp /= /applybig.
induction (ord_enum ); simpl; auto.
rewrite {1}/Basics.flip.
rewrite Rplus_comm.
change Algebra.add with Rplus.
f_equal; auto.
Qed.

Lemma perturb_sum: forall (a b: 'I_n ->R) (c: R) ,
  (forall i, Rabs (a i - b i) <= c) ->
  Rabs ((\sum_(i<n) a i) - (\sum_(i<n) b i)) <= (Rmult (INR n) c).
Admitted.

Lemma feq_FT2R: forall x y: ftype t, feq x y -> FT2R x = FT2R y.
 (* TODO: this is already in VCFloat somewhere, or should be *)
Proof.
intros.
destruct x, y; try destruct s; try reflexivity; try inversion H;
destruct H1; subst; auto.
Qed.


Lemma big_sum_const_seq I (r : seq I) x : (\sum_(i <- r) x = INR (size r) * x)%Re.
Proof.
elim: r=> [|e r IHr].
{ by rewrite big_nil /= Rmult_0_l. }
by rewrite big_cons S_INR Rplus_comm Rmult_plus_distr_r Rmult_1_l IHr.
Qed.

Lemma big_sum_const x : (\sum_(i < n) x = INR n * x)%Re.
Proof.
by rewrite big_sum_const_seq /= /index_enum /= -enumT size_enum_ord.
Qed.

Lemma Rle_big_compat I (F F' : I -> R) r :
  (forall i, F i <= F' i) -> (\sum_(i <- r) F i <= \sum_(i <- r) F' i).
Proof.
move=> H.
apply /RleP.
apply (@big_rec2 R R Order.le Algebra.zero Algebra.add  Algebra.zero Algebra.add (le_refl _) I r
 (fun=>true)).
intros.
 rewrite /GRing.add /=.
apply /RleP. apply Rplus_le_compat; apply /RleP;  auto. apply /RleP. auto.
Qed.

Lemma integrate_model_err_partial: 
     Rabs (FT2R integrate_model_f - integrate_model_r) <= integrate_model_acc.
Proof.
 intros.
  rewrite /integrate_model_f  /integrate_model_r.
  pose c := (INR n * maxwf)%Re.
  assert (
    Rabs
       (Rminus (\sum_(i < nat_of_ord n) FT2R (BMULT (gauss_wt_f i) (f (gauss_pt_f i))))
            (\sum_(i < nat_of_ord n) gauss_wt n i * g (gauss_pt n i)))
            <=   c).
   apply perturb_sum; intro; apply (proj2 (gauss_pt_wt_acc i)).
 set a1 := \sum_(i < nat_of_ord n) gauss_wt n i * g (gauss_pt n i) in H|-*. clearbody a1. simpl in a1.
  pose proof Fsum_forward_error (fun i => BMULT (gauss_wt_f i) (f (gauss_pt_f i)))
    Fsum_gauss_wt_pt_finite.
 set a2 := bigop _ _ _ in H,H0. clearbody a2.
 set a3 := FT2R (F.sum _) in H0.
 set a3' := FT2R (dotprodF _ _).
 assert (a3' = a3). {
  rewrite /a3 /a3'.
 rewrite /dotprod.
 apply feq_FT2R.
 rewrite dotprodF_dotprodF'_feq.
 match goal with |- feq ?A ?B => replace B with A; [auto | ] end.
 rewrite /dotprodF'  F.sum_sumF.
 rewrite /dotprod_model.dotprod /sumF.
 f_equal.
 induction (ord_enum _); simpl; rewrite ?ffunE; f_equal; auto.
}
 clearbody a3'. subst a3'.
 clearbody a3.
 set a4 := bigop _ _ _ in H0.
simpl in a4.
assert (a4 <= INR n * (2 * fb + maxwf)). {
   rewrite /a4.
  apply /RleP.
 eapply le_trans with (\sum_(i < nat_of_ord n) (2 * fb + maxwf)).
 apply /RleP.
 apply Rle_big_compat. 
 intro. apply gauss_pt_wt_bound.
 rewrite big_sum_const.
 apply le_refl.
}
clearbody a4.
 replace (a3-a1) with ((a3-a2) + (a2-a1)) by lra.
 eapply Rle_trans; [ apply Rabs_triang | ].
 rewrite (Rabs_minus_sym a3).
 eapply Rle_trans; [ apply Rplus_le_compat; try eassumption | ].
 eapply Rle_trans; [ apply Rplus_le_compat; [ | reflexivity] | ].
 apply Rmult_le_compat_l.
 apply g_pos. apply H1.
 subst c.
 reflexivity.
Qed.

 Lemma integrate_model_err: 
     Rabs (FT2R integrate_model_f - ∫ g) <= integrate_model_acc + b. {
Proof.
 intros.
 replace (FT2R integrate_model_f - ∫ g) with
    (FT2R integrate_model_f - integrate_model_r + (integrate_model_r - ∫ g))
  by lra.
 etransitivity; [apply Rabs_triang | ].
 apply Rplus_le_compat.
 apply integrate_model_err_partial.
 apply quadrature_error_bound_is_bound in Hb.
 rewrite Rabs_minus_sym.
 replace integrate_model_r with (Gauss_Legendre_quadrature n g). 2:{
   rewrite /Gauss_Legendre_quadrature /integrate_model_r /compute_G.
   apply eq_big => i; auto. move => _.
   rewrite /gauss_wt /gauss_pt.
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

Module Quadmodel_F64.


Definition gauss_pts_list : list (ftype Tdouble) :=
  [      (* One point *)
         0.0;

        (* Two points *)
        -0.5773502691896257;
        0.5773502691896257;

        (* Three points *)
        -0.7745966692414834;
        0.0;
        0.7745966692414834;

        (* Four points *)
        -0.8611363115940526;
        -0.33998104358485626;
        0.33998104358485626;
        0.8611363115940526;

        (* Five points *)
        -0.906179845938664;
        -0.538469310105683;
        0.0;
        0.538469310105683;
        0.906179845938664;

        (* Six points *)
        -0.932469514203152;
        -0.661209386466265;
        -0.238619186083197;
        0.238619186083197;
        0.661209386466265;
        0.932469514203152;

        (* Seven points *)
        -0.949107912342759;
        -0.741531185599394;
        -0.405845151377397;
        0.0;
        0.405845151377397;
        0.741531185599394;
        0.949107912342759;

        (* Eight points *)
        -0.960289856497536;
        -0.796666477413627;
        -0.525532409916329;
        -0.183434642495650;
        0.183434642495650;
        0.525532409916329;
        0.796666477413627;
        0.960289856497536;

        (* Nine points *)
        -0.968160239507626;
        -0.836031107326636;
        -0.613371432700590;
        -0.324253423403809;
        0.0;
        0.324253423403809;
        0.613371432700590;
        0.836031107326636;
        0.968160239507626;

        (* Ten points *)
        -0.973906528517172;
        -0.865063366688985;
        -0.679409568299024;
        -0.433395394129247;
        -0.148874338981631;
        0.148874338981631;
        0.433395394129247;
        0.679409568299024;
        0.865063366688985;
        0.973906528517172
  ]%F64.

(** The C program has a local static array containing all these values in this order: *)
Definition gauss_wts_list : list (ftype Tdouble) := [
        (* One point *)
        2.0;

        (* Two points *)
        1.0;
        1.0;

        (* Three points *)
        0.5555555555555556;
        0.8888888888888889;
        0.5555555555555556;

        (* Four points *)
        0.34785484513745384;
        0.65214515486254616;
        0.65214515486254616;
        0.34785484513745384;

        (* Five points *)
        0.236926885056189;
        0.478628670499366;
        0.568888888888889;
        0.478628670499366;
        0.236926885056189;

        (* Six points *)
        0.171324492379170;
        0.360761573048139;
        0.467913934572691;
        0.467913934572691;
        0.360761573048139;
        0.171324492379170;

        (* Seven points *)
        0.129484966168870;
        0.279705391489277;
        0.381830050505119;
        0.417959183673469;
        0.381830050505119;
        0.279705391489277;
        0.129484966168870;

        (* Eight points *)
        0.101228536290376;
        0.222381034453374;
        0.313706645877887;
        0.362683783378362;
        0.362683783378362;
        0.313706645877887;
        0.222381034453374;
        0.101228536290376;

        (* Nine points *)
        0.081274388361574;
        0.180648160694857;
        0.260610696402935;
        0.312347077040003;
        0.330239355001260;
        0.312347077040003;
        0.260610696402935;
        0.180648160694857;
        0.081274388361574;

        (* Ten points *)
        0.066671344308688;
        0.149451349150581;
        0.219086362515982;
        0.269266719309996;
        0.295524224714753;
        0.295524224714753;
        0.269266719309996;
        0.219086362515982;
        0.149451349150581;
        0.066671344308688
  ]%F64.


Definition half_an_ulp : R := FPCore.default_rel (coretype_of_type Tdouble).

Definition float_near (r: R) (x: ftype Tdouble) :=
  (Rabs (FT2R x - r) <= Rabs (FT2R x) * half_an_ulp)%R.

Require Import VST.floyd.functional_base.

Definition gauss_weight_f [n: 'I_5] (i: 'I_n) := 
    Znth ((Z.of_nat n)*(Z.of_nat n - 1)/2 + Z.of_nat i) gauss_wts_list.

Definition gauss_point_f [n: 'I_5] (i: 'I_n) := 
    Znth ((Z.of_nat n)*(Z.of_nat n - 1)/2 + Z.of_nat i) gauss_pts_list.

Lemma gauss_points_acc: forall (n: 'I_5) (i: 'I_n),  float_near (gauss_pt n i) (gauss_point_f i).
Proof.
intros [n Hn] [i Hi]; simpl in *.
destruct n as [ | [ | [ | [ | [ |] ]]]]; try lia;
destruct i as [ | [ | [ | [ | [ |] ]]]]; try lia;
red;
set (d := half_an_ulp); hnf in d; simpl in d; subst d;
unfold gauss_pt, gauss_point_f, tuple.tnth; simpl;
 prepare_for_interval; simpl;
rewrite <- ?Rstruct.RsqrtE, <- ?Rstruct.INRE, ?Rminus_diag;
first [rewrite ?Rabs_R0; Lra.lra | interval with (i_prec(110%positive))].
Qed.

Lemma gauss_weights_acc: forall (n: 'I_5) (i: 'I_n),  float_near (gauss_wt n i) (gauss_weight_f i).
Proof.
intros [n Hn] [i Hi]; simpl in *.
destruct n as [ | [ | [ | [ | [ |] ]]]]; try lia;
destruct i as [ | [ | [ | [ | [ |] ]]]]; try lia;
red;
set (d := half_an_ulp); hnf in d; simpl in d; subst d;
unfold gauss_wt, gauss_weight_f, tuple.tnth; simpl;
 prepare_for_interval; 
first [rewrite ?Rabs_R0; Lra.lra | interval with (i_prec(110%positive))].
Qed.

Open Scope R_scope.

Lemma gauss_point_f_bound [n: 'I_5]: 
  (forall i : 'I_n, Rabs (FT2R (gauss_point_f i)) <= 1).
Proof.
revert n.
intros [n Hn] [i Hi]; simpl in *.
destruct n as [ | [ | [ | [ | [ |] ]]]]; try lia;
destruct i as [ | [ | [ | [ | [ |] ]]]]; try lia;
simpl; interval.
Qed.

Lemma gauss_point_f_acc [n: 'I_5]: gauss_pts_accuracy Tdouble _ (@gauss_point_f n).
Proof.
red; intros; unfold quadmodel_accuracy.finite.
pose proof gauss_points_acc n i.
red in H.
split.
-
clear.
destruct n as [n Hn]; destruct i as [i Hi];
destruct n as [ | [ | [ | [ | [ |] ]]]]; try lia;
destruct i as [ | [ | [ | [ | [ |] ]]]]; try lia;
simpl; auto.
-
unfold half_an_ulp, FPCore.default_rel in *; simpl in *.
pose proof gauss_point_f_bound i.
set x := (FT2R (gauss_point_f i)) in H,H0|-*.
clearbody x. 
set (y := quadrature2.gauss_pt n i) in H|-*.
clearbody y.
prepare_for_interval.
simpl in *.
change (Rplus x (Ropp y)) with (Rminus x y).
etransitivity. apply H.
clear H.
set (z := (/2 * _)).
assert (0 <= z) by (unfold z; lra).
unfold default_rel; simpl.
change (/ _ * / _) with z.
clearbody z.
transitivity (1 * z); [ | lra].
apply Rmult_le_compat_r; auto.
Qed.


Lemma gauss_weight_f_acc [n: 'I_5]: gauss_wts_accuracy Tdouble _ (@gauss_weight_f n).
Proof.
red; intros; unfold quadmodel_accuracy.finite.
pose proof gauss_weights_acc n i.
red in H.
split.
-
clear.
destruct n as [n Hn]; destruct i as [i Hi];
destruct n as [ | [ | [ | [ | [ |] ]]]]; try lia;
destruct i as [ | [ | [ | [ | [ |] ]]]]; try lia;
simpl; auto.
-
unfold half_an_ulp, FPCore.default_rel in *; simpl in *.
assert ((n>1)%nat -> (0 <= FT2R (gauss_weight_f i) <= 1)%R). {
clear.
destruct n as [n Hn]; destruct i as [i Hi];
destruct n as [ | [ | [ | [ | [ |] ]]]]; try lia;
destruct i as [ | [ | [ | [ | [ |] ]]]]; try lia;
unfold gauss_weight_f; simpl nat_of_ord;
intro; try discriminate;
set z := (Znth _ _); hnf in z; subst z;
compute; lra.
}
destruct n as [n Hn].
destruct n as [ | [ | n]].
+ (* n=0 *)
simpl in i; destruct i; lia.
+ (* n=1 *)
clear.
simpl in i.
rewrite ord1. clear i.
unfold gauss_weight_f, quadrature2.gauss_wt.
simpl.
unfold reverse_coercion; simpl.
unfold tuple.tnth, tuple.cons_tuple; simpl.
prepare_for_interval.
transitivity 0; simpl; try lra.
unfold Defs.F2R. simpl.
replace (_ - _) with 0 by lra.
rewrite Rabs_R0. lra.
compute; lra.
+
specialize (H0 (eq_refl _)).
change (Binary.B2R _ _ (gauss_weight_f i)) with (FT2R (gauss_weight_f i)).
set x := (FT2R (gauss_weight_f i)) in H,H0|-*.
clearbody x. 
set (y := quadrature2.gauss_wt _ i) in H|-*.
clearbody y.
prepare_for_interval.
simpl in *.
change (Rplus x (Ropp y)) with (Rminus x y).
etransitivity. apply H.
clear H.
set (z := (/2 * _)).
assert (0 <= z) by (unfold z; lra).
change default_rel with z.
clearbody z.
transitivity (1 * z); [ | lra].
apply Rmult_le_compat_r; auto.
apply Rabs_le.
lra.
Qed.

Lemma gauss_weight_f_range [n]: gauss_wt_f_range Tdouble _ (@gauss_weight_f n).
Proof.
red; intros.
destruct n as [n Hn]; destruct i as [i Hi];
destruct n as [ | [ | [ | [ | [ |] ]]]]; try discriminate;
destruct i as [ | [ | [ | [ | [ |] ]]]]; try discriminate;
compute; lra.
Qed.

End Quadmodel_F64.
