(** * CFEM.quadrature2:  Computation of quadrature error bounds *)
From mathcomp Require Import all_boot ssralg ssrnum archimedean finfun order.
From mathcomp Require Import all_algebra  all_field all_analysis all_reals.
Import Order.TTheory GRing.Theory Num.Theory GRing.
From mathcomp.algebra_tactics Require Import ring lra.
Import classical_sets.
Import numFieldNormedType.Exports.
From Stdlib Require Import FunctionalExtensionality.
From CFEM Require Import quadrature.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Local Open Scope R_scope.
Local Open Scope order_scope.
Local Open Scope ring_scope.

Import Legendre.
Require Import Interval.Tactic.
From mathcomp Require Import Rstruct.
Import trigo.

Local Notation R := (RbaseSymbolsImpl_R__canonical__reals_Real).

 Notation "∫" := intgal.

(* Because [derivable] is not locked, many simple kinds of proofs will tend to blow up.
  See this: https://rocq-prover.zulipchat.com/#narrow/channel/237666-math-comp-analysis/topic/very.20slow.20unification.20failure.2C.20derivable_sin.2C.20derivable_cos/with/612359969
  So at (* this line *) below, we must explicitly [apply H] instead of doing [assumption] or [auto].
  And also, Hint Resolve databases won't work.
*)


Lemma derive1M (f g: R -> R) (x: R) :
  derivable f x 1 ->
  derivable g x 1 ->
  (f  \* g)^`()%classic x = f x * g^`()%classic x + f^`()%classic x * g x.
Proof.
intros.
progress simpl.
rewrite ?derive1E.
rewrite deriveM.
-
f_equal.
rewrite mulrC.
rewrite /scale //.
-
apply H.  (* this line *)   (* see comment above *)
-
apply H0.
Qed.

Definition everywhere_derivable (f: R -> R) := forall x, derivable f x 1.

Lemma derive1M_ (f g: R -> R) :
  everywhere_derivable f ->
  everywhere_derivable g ->
  (mul_fun f g)^`()%classic = add_fun (mul_fun f (g^`()%classic)) (mul_fun (f^`()%classic) g).
Proof.
intros.
extensionality x.
rewrite derive1M; auto.
Qed.

Notation d1 := (@derive1 R (Real_sort__canonical__normed_module_NormedModule RbaseSymbolsImpl_R__canonical__reals_Real)).

Lemma derive1_cst': forall [V : normedModType R] (k : V) (t : R), 
   (fun=> k)^`()%classic t = 0.
Proof. intros; apply derive1_cst. Qed.

Lemma derive1_cos: d1 cos = opp_fun sin.
Proof.
extensionality x.
rewrite derive1E.
destruct (mathcomp.analysis.trigo.is_derive_cos x).
auto.
Qed.

Lemma derive1_sin: d1 sin = cos.
Proof.
extensionality x.
rewrite derive1E.
destruct (mathcomp.analysis.trigo.is_derive_sin x).
auto.
Qed.

Lemma derive1_add: forall (f g : R -> R), 
  everywhere_derivable f ->
  everywhere_derivable g ->
  d1 (f \+ g) = (d1 f \+ d1 g).
Proof.
intros.
extensionality x.
rewrite /= ?derive1E.
rewrite deriveD.
auto.
apply H.
apply H0.
Qed.

Lemma derive1_opp: forall (f : R -> R), 
  everywhere_derivable f->
  d1 (\- f) = \- (d1 f).
Proof.
intros.
extensionality x.
rewrite /= ?derive1E.
rewrite deriveN //.
Qed.

Lemma opp_funK: forall f: R -> R, opp_fun (opp_fun f) = f.
Proof.
intros.
extensionality x.
simpl.
rewrite opprK //.
Qed.

Lemma ev_deriv_cos: everywhere_derivable cos.
Proof.
intro.
apply derivable_cos.
Qed.

Lemma ev_deriv_sin:  everywhere_derivable sin.
Proof.
intro.
apply derivable_sin.
Qed.

Lemma range_Rabs: forall x, is_true (-1 <= x <= 1) -> Rdefinitions.Rle (Rbasic_fun.Rabs x) 1.
Proof.
intros.
apply Stdlib.Rabs_def1_le; apply /RleP.
lra.
change (is_true (- 1 <= x)). lra.
Qed.

Lemma derivE_rev :
forall (p : {poly Num_RealField__to__GRing_NzSemiRing R}),
 (horner p)^`()%classic = horner p^`().
Proof. intros. symmetry. apply derivE. Qed.

Lemma ev_deriv_horner: forall p: {poly R}, everywhere_derivable (horner p).
Proof.
intros. intro. apply derivable_horner.
Qed.

Lemma ev_derivD: forall  (f g: R -> R),
    everywhere_derivable f -> everywhere_derivable g -> everywhere_derivable (f \+ g).
Proof.
intros. intro. apply (@derivableD _ _ _ f g); auto.
Qed.

Lemma ev_derivB: forall  (f g: R -> R),
    everywhere_derivable f -> everywhere_derivable g -> everywhere_derivable (f \- g).
Proof.
intros. intro. apply (@derivableB _ _ _ f g); auto.
Qed.

Lemma ev_derivN: forall (f : R -> R),
    everywhere_derivable f -> everywhere_derivable (\- f).
Proof.
intros. intro. apply derivableN; auto.
Qed.

Lemma ev_derivM: forall (f g: R -> R),
    everywhere_derivable f -> everywhere_derivable g -> everywhere_derivable (f \* g).
Proof.
intros. intro. apply derivableM; auto.
Qed.

Lemma ev_deriv_cst: forall (c: R),
    everywhere_derivable (functions.cst c).
Proof.
intros. intro. apply derivable_cst.
Qed.

Ltac derivable := 
  with_strategy opaque [derive.derivable]  
  solve [repeat first
    [ simple apply ev_deriv_cos
    | simple apply ev_deriv_sin
    | simple apply ev_deriv_horner
    | simple apply ev_derivD
    | simple apply ev_derivB
    | simple apply ev_derivN 
    | simple apply ev_derivM 
    | simple apply ev_deriv_cst 
   ]].


Definition r_deriv := (@deriv0, @derivMn, @derivZ, @derivMz, @deriv_mulC, @derivXn, @derivX, @derivC, @derivXsubC, @derivMXaddC, @derivMNn, @derivM, @derivD, @derivB, @derivN, @deriv_exp).

Definition r_derive1 := (derive1_cos, derive1_sin, derivE_rev, derivMXaddC, derivC,
         @horner0_ext R).

Import Rewriting. 

Ltac rewrite_derive1_bottom_up := 
 match goal with
  |  |- context [derive1 (mul_fun ?f ?g)] => 
         lazymatch f with context [derive1] => fail | _ => idtac end;
         lazymatch g with context [derive1] => fail | _ => idtac end;
         rewrite (derive1M_ f g); [ | derivable ..]
  |  |- context [derive1 (add_fun ?f ?g)] => 
         lazymatch f with context [derive1] => fail | _ => idtac end;
         lazymatch g with context [derive1] => fail | _ => idtac end;
         rewrite (derive1_add f g); [ | derivable ..]
  |  |- context [derive1 (opp_fun ?f)] => 
         lazymatch f with context [derive1] => fail | _ => idtac end;
         rewrite (derive1_opp f); [ | derivable ..]
 end.

Ltac rewrite_derive := 
  repeat (
  simpl;
  first [rewrite !(r_derive1, r_ring, r_lift, opp_funK)
         | rewrite_derive1_bottom_up
         ]).

Lemma true_andb_e1: forall [A B],
 is_true (andb A B) -> is_true A.
Proof.
intros. red in H. rewrite Bool.andb_true_iff in H. apply H.
Qed.

Lemma true_andb_e2: forall [A B],
 is_true (andb A B) -> is_true B.
Proof.
intros. red in H. rewrite Bool.andb_true_iff in H. apply H.
Qed.

Lemma conj': forall A B C, (A /\ B -> C) -> (A -> B -> C).
Proof. tauto. Qed.

Ltac massage_constraints := 
repeat match goal with 
|  H: is_true (?A ?B) |- _ => 
   move :(true_andb_e2 H);  first [move /RltbP | move /RlebP];
   move :(true_andb_e1 H);  first [move /RltbP | move /RlebP];
   apply conj'; clear H; move => H
end.

Lemma trigo_cos_e: (@cos.body RbaseSymbolsImpl_R__canonical__reals_Real) = Rtrigo_def.cos.
(* See: https://rocq-prover.zulipchat.com/#narrow/channel/237666-math-comp-analysis/topic/relating.20trigo.2Ecos.20to.20Rtrigo_def.2Ecos.2C.20etc.2E/with/612420101 *)
Admitted.

Lemma trigo_sin_e: (@sin.body RbaseSymbolsImpl_R__canonical__reals_Real) = Rtrigo_def.sin.
(* See: https://rocq-prover.zulipchat.com/#narrow/channel/237666-math-comp-analysis/topic/relating.20trigo.2Ecos.20to.20Rtrigo_def.2Ecos.2C.20etc.2E/with/612420101 *)
Admitted.

Ltac prepare_for_interval := 
lazymatch goal with |- is_true (?A <= ?B <= ?C) => 
    let H0 := fresh "H0" in let H1 := fresh "H1" in 
   assert (H0: Rdefinitions.Rle A B /\ Rdefinitions.Rle B C);
    [ | destruct H0 as [H0 H1]; move :H0 => /RleP H0; move :H1 => /RleP H1; rewrite H0 H1 // ]
 | _ => idtac
 end;
rewrite ?trigo_cos_e ?trigo_sin_e; 
change nmodule.Algebra.zero with (Raxioms.INR O)  in *;
repeat change (ssralg.GRing.mul ?A ?B) with (Rdefinitions.Rmult A B) in *;
repeat change (nmodule.Algebra.opp ?A) with (Rdefinitions.Ropp A) in *;
repeat change (nmodule.Algebra.add ?A ?B) with (Rdefinitions.Rplus A  B) in *;
repeat change (GRing.one _) with (Raxioms.INR 1%nat) in *;
repeat change (GRing.inv ?A) with (Rdefinitions.Rinv A)%R in * ;
rewrite <- ?Rstruct.RsqrtE, <- ?Rstruct.INRE, ?RIneq.Rminus_diag in *;
lazymatch goal with
 |  |- is_true (@Order.lt _ RbaseSymbolsImpl_R__canonical__Order_Preorder _ _) => apply /RltbP
 |  |- is_true (@Order.le _ RbaseSymbolsImpl_R__canonical__Order_Preorder _ _) => apply /RlebP
 |  |- _ => idtac
end;
massage_constraints.


Definition gauss_pt (n: 'I_5) (i: 'I_n) :=
      tuple.tnth (@ROOTS_vals  R lo hi w n (LR_roots n (nth_iseq some_legendre_roots n))) i.

Lemma gauss_pt_range: forall n i,  -1 <= gauss_pt n i <= 1.
 Proof.
 move => [n Hn] [i Hi]; simpl in *.
destruct n as [ | [ | [ | [ | [ |] ]]]]; try Lia.lia;
destruct i as [ | [ | [ | [ | [ |] ]]]]; try Lia.lia;
 rewrite /gauss_pt /tnth /=;
 clear; try lra;
 prepare_for_interval; interval.
Qed.

Definition gauss_wt (n: 'I_5) (i: 'I_n) :=
 tuple.tnth (@GW_vals R _ (nth_iseq some_gauss_weights n)) i.

Lemma gauss_wt_range: forall n i, 0 <= gauss_wt n i <= 2.
 Proof.
 move => [n Hn] [i Hi]; simpl in *.
destruct n as [ | [ | [ | [ | [ |] ]]]]; try Lia.lia;
destruct i as [ | [ | [ | [ | [ |] ]]]]; try Lia.lia;
 rewrite /gauss_wt /tnth /=;
 clear; try lra;
 prepare_for_interval;interval.
Qed.

Definition r_intgal_C := (@intgal_linearN, @r_intgal, @intgal_C, @hornerC').

Definition legendre_integral2 (n: nat) : Type := {s : Real.sort R |  ∫ (fun x : Real.sort R => (legendre n).[x] ^ 2) = s }.

Ltac prove_legendre_integral2 :=
change (fun x : _ => exprz (?A x) 2) with (mul_fun A A);
rewrite -hornerM';
rewrite ?(@mulrD  (poly_polynomial__canonical__GRing_PzSemiRing _)) -?mulrA ?r_intgal;
repeat match goal with |- context [ 'X * polyC ?a ] => rewrite ?(pull_left (polyC a)) end;
repeat match goal with |- context [ 'X * (polyC ?a * _)] => rewrite ?(pull_left (polyC a)) end;
rewrite ?r_intgal;
lra.

Definition legendre_integral2_iseq : iseq legendre_integral2 5.
repeat eapply i_cons; try apply i_nil.
- exists (128/11025); rewrite Legendre_poly_4;  abstract prove_legendre_integral2.
- exists (8/175); rewrite Legendre_poly_3; abstract prove_legendre_integral2.
- exists (8/45); rewrite Legendre_poly_2; abstract prove_legendre_integral2.
- exists (2/3);  rewrite Legendre_poly_1; abstract prove_legendre_integral2.
- exists 2; rewrite Legendre_poly_0; abstract prove_legendre_integral2.
Defined.

Import BinInt.
Notation IZR := (Rdefinitions.IZR).

Ltac eval_legendre_integral2 :=
match goal with |- context [@legendre ?R ?N] => 
   let n := eval compute in N in change (@legendre R N) with (@legendre R n);
    let x := fresh "x" in let e := fresh "e" in let H := fresh in 
    destruct (nth_iseq legendre_integral2_iseq (@Ordinal 5 n isT)) as [x e] eqn:H;
    injection H; clear H; move => H; rewrite {}e -{}H; clear x
end.

Ltac gauss_legendre_error_bounder := 
red; intros;
eval_legendre_integral2;
let j := fresh "j" in set j := factorial _; compute in j; subst j;
simpl derive1n;
match goal with |- is_true (_ <= ?A) => set j := A end;
rewrite_derive;
rewrite ?r_deriv ?r_ring ?hornerE /= ?r_ring ?mulrN ?mulNr ?opprK ?r_ring ler_norml;
subst j;
prepare_for_interval; 
interval.

Lemma error_1_0_1':
 (* test function (1/2)*(1-x)*cos(x), degree-1 quadrature *)
 quadrature_error_bound (horner ((1/2)%:P *(1-'X)) \* cos) 1 (IZR 2 / IZR 100).
Proof.
time "error_1_0_1" gauss_legendre_error_bounder.  (* 3.444 seconds *)
Qed.

(* Our test case is the product of a Lagrange shape function (1/2)*(1-x) with some 
  spatial transformation, in this case cosine. *)

Lemma error_1_0_1:
 (* test function (1/2)*(1-x)*cos(x), degree-1 quadrature *)
 let f :=horner ((1/2)%:P *(1-'X)) \* cos in 
 `| ( ∫ f - Gauss_Legendre_quadrature 1 f ) | <= IZR 2 / IZR 100.
Proof.
apply quadrature_error_bound_is_bound.
time "error_1_0_1" gauss_legendre_error_bounder.  (* 3.444 seconds *)
Qed.

Lemma error_1_0_2:
 (* test function (1/2)*(1-x)*cos(x), degree-2 quadrature *)
 let f :=horner ((1/2)%:P *(1-'X)) \* cos in 
 `| ( ∫ f - Gauss_Legendre_quadrature 2 f ) | <=  IZR 223 / IZR 100000.
Proof.
apply quadrature_error_bound_is_bound.
time "error_1_0_2" gauss_legendre_error_bounder.  (* 31.7 seconds *)
Qed.


Definition deriv_bound (f: R -> R) (b: R) :=
  forall x, (-1 <= x <= 1) -> (`| derive.derive1 f x | <= b).


