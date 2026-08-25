(** * CFEM.quadrature:  Gaussian quadrature, following G. W. Stewart *)
From mathcomp Require Import all_boot ssralg ssrnum archimedean finfun order.
From mathcomp Require Import all_algebra  all_field all_analysis all_reals.
Import Order.TTheory GRing.Theory Num.Theory GRing.
From mathcomp.algebra_tactics Require Import ring lra.
Import classical_sets.
Import numFieldNormedType.Exports.
From Stdlib Require Import FunctionalExtensionality.

Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

Local Open Scope R_scope.
Local Open Scope order_scope.
Local Open Scope ring_scope.


(** First, some preliminaries *)

(* begin details : Many general-purpose supporting lemmas, not specific to quadrature *)

Lemma size_behead: forall {A} [n] (x: (n.+1).-tuple A), size (behead x) == n.
Proof. intros; rewrite size_behead size_tuple //. Qed.

Definition tuple_behead {A} [n] (x: n.+1.-tuple A) : n.-tuple A :=
  Tuple (size_behead x).

Lemma tuple_ext: forall {A}[n] (x y: n.-tuple A), tval x = tval y -> x=y. 
Proof.
intros.
destruct x as [x Hx]; destruct y as [y Hy]; simpl in *; subst x. f_equal.
apply eq_irrelevance.
Qed.

Lemma tuple_rehead {A} [n] (x: n.+1.-tuple A): cons_tuple (thead x) (tuple_behead x) = x.
Proof.
apply tuple_ext.
simpl.
pose proof tuple_eta x. symmetry.
destruct x; simpl in H. inversion  H. simpl. auto.
Qed.


Lemma sorted_ij {R: realType}: 
 forall (rl: list R) (i j: nat) (d1 d2: R),
  is_true (sorted <%R rl) ->
  is_true (i < size rl)%N ->
  is_true (j < size rl)%N ->
  (nth d1 rl i < nth d2 rl j)%R = (i < j)%N.
Proof.
intros.
revert i j H0 H1; induction rl; intros.
simpl in H0; Lia.lia.
simpl in H0,H1.
destruct i,j; simpl in *.
-
rewrite ltnn lt_irreflexive //.
-
rewrite ltn0Sn.
 apply order_path_min in H; [ | intros ? ? ?; lra].
  pose proof (@all_nthP _  (> a)  rl d2). rewrite H in H2. inversion H2.
  rewrite H3; auto.
-
 replace (i.+1<0)%N with false by Lia.lia.
 apply order_path_min in H; [ | intros ? ? ?; lra].
  pose proof (@all_nthP _  (> a)  rl d1). rewrite H in H2. inversion H2.
  assert (is_true (i<size rl)%N). Lia.lia.
  specialize (H3 _ H4). lra.
-
 rewrite IHrl; auto.
 apply path_sorted in H; auto.
Qed.

Module Rewriting.

 Section R.
 Context {R : realType}.

Lemma hornerXsubC': forall [R : nzRingType] (a : NzRing.sort R), horner('X - a%:P) = (id \- fun=>a).
Proof.
intros. extensionality x. apply hornerXsubC.
Qed.

Lemma hornerX': forall {R : nzSemiRingType}, @horner R ('X) = id.
Proof.
intros. extensionality x. apply hornerX.
Qed.

Lemma hornerC': forall (c: R), horner (polyC c) = (fun=>c).
Proof. intros. extensionality x. apply hornerC.
Qed.

Lemma hornerD': forall [R] (a b: {poly R}), horner (a+b) = horner a \+ horner b.
Proof. intros. extensionality x. apply hornerD.
Qed.

Lemma hornerM': forall [R: comNzSemiRingType] (a b: {poly R}), horner (a*b) = horner a \* horner b.
Proof. intros. extensionality x. apply hornerM.
Qed.

Lemma hornerN': forall [R: nzRingType] (a: {poly R}), horner (- a) = \- horner a.
Proof. intros. extensionality x. apply hornerN.
Qed.

Definition r_horner := (@hornerXsubC, @hornerXsubC', @hornerX, @hornerX', @hornerC, @hornerC',
                                      @hornerD, @hornerD', @hornerM, @hornerM', @hornerN, @hornerN').

Lemma mul_fun1r: forall
   {R : PzSemiRing.type} {T : Type} (f: T -> PzSemiRing.sort R),
    mul_fun (fun=>1) f = f.
Proof.
intros. extensionality x. simpl. apply mul1r.
Qed.

Lemma mul_funr1: forall
   {R : PzSemiRing.type} {T : Type} (f: T -> PzSemiRing.sort R),
    mul_fun f (fun=>1) = f.
Proof.
intros. extensionality x. simpl. apply mulr1.
Qed.
Hint Rewrite @mul1r @mul_fun1r @mulr1 @mul_funr1 : horner.

Lemma mul_fun0r: forall
   {R : PzSemiRing.type} {T : Type} (f: T -> PzSemiRing.sort R),
    mul_fun (fun=>0) f = (fun=>0).
Proof.
intros. extensionality x. simpl. apply mul0r.
Qed.

Lemma mul_funr0: forall
   {R : PzSemiRing.type} {T : Type} (f: T -> PzSemiRing.sort R),
    mul_fun f (fun=>0) = (fun=>0).
Proof.
intros. extensionality x. simpl. apply mulr0.
Qed.
Hint Rewrite @mul0r @mul_fun0r @mulr0 @mul_funr0 : horner.

Lemma opp_funC: forall  {U : Type} {V : BaseZmodule.type} (c: V), 
  @opp_fun U V (fun=>c) = (fun=> opp c).
Proof.
intros. extensionality x. reflexivity.
Qed.

Lemma opp_funr0:  forall {U: Type}, (fun _:U=> (-0):R) = (fun _:U => 0:R).
Proof.
intros. extensionality x. apply oppr0.
Qed.

Lemma sub_funr0: forall {U: Type} {V: zmodType} (f: U -> V),
  sub_fun f (fun=>0) = f.
Proof. intros. extensionality x. simpl. apply subr0.
Qed.

Lemma add_fun0r: forall {U: Type} {V: nmodType} (f: U -> V),
  add_fun (fun=>0) f = f.
Proof. intros. extensionality x. simpl. apply add0r.
Qed.

Lemma add_funr0: forall {U: Type} {V: nmodType} (f: U -> V),
  add_fun f (fun=>0) = f.
Proof. intros. extensionality x. simpl. apply addr0.
Qed.

Lemma mul_funDr: forall  {s : pzSemiRingType} {T: Type},
   @right_distributive (T -> PzSemiRing.sort s) _ mul_fun add_fun.
Proof. intros. red. intros. extensionality i. simpl. apply mulrDr. Qed.

Lemma mul_funDl: forall  {s : pzSemiRingType} {T: Type},
   @left_distributive (T -> PzSemiRing.sort s) _ mul_fun add_fun.
Proof. intros. red. intros. extensionality i. simpl. apply mulrDl. Qed.

Lemma mul_funA: forall  {s : pzSemiRingType} {T: Type},
   @associative (T -> PzSemiRing.sort s) mul_fun.
Proof. intros. red. intros. extensionality i. simpl. apply mulrA. Qed.

Lemma mul_funC: forall  {s : comPzSemiRingType} {T: Type},
   @commutative (T -> s) _ mul_fun.
Proof. intros. red. intros. extensionality i. simpl. apply mulrC. Qed.

Lemma mul_fun_consts: forall {s : comPzSemiRingType} {T: Type} (a b: s),
    @mul_fun s T (fun=>a) (fun=>b) = fun=> a*b.
Proof. intros; extensionality i; auto. Qed.

Definition r_ring := (@mulr1, @mul1r, @mulr0, @mul0r, @addr0, @add0r, @oppr0, @subr0).
Definition r_lift := (@mul_funr1, @mul_fun1r, @mul_funr0, @mul_fun0r, @mul_fun_consts,
                               @add_funr0, @add_fun0r, @opp_funr0, @sub_funr0, @opp_funC).

Lemma hornerX_i: (fun x: Real.sort R => x) = (@horner (reals_Real__to__GRing_NzSemiRing R) 'X).
Proof. extensionality x. rewrite hornerX //. Qed.

Lemma poly0 {F: Num.NumDomain.type}: forall f, @poly  F 0 f = 0.
Proof.
intros.
unlock poly.
rewrite locked_withE /poly_expanded_def /= polyC0 //.
Qed.

Lemma mul_polyC': forall a b: R, polyC a * polyC b = polyC (a*b).
Proof.
intros.
rewrite mul_polyC scale_polyC //.
Qed.

Lemma polyCN: forall  (x:R), polyC(opp x) = - polyC x.
Proof. intros.
rewrite -scaleN1r -scale_polyC scaleN1r //.
Qed.

Definition polynil: {poly R} := @Polynomial _ nil oner_neq0.
Lemma polynil_eq: polynil=0.
Proof.
apply /eqP.
rewrite -nil_poly //.
Qed.

Lemma polyC1': 1%:P = @Polynomial R [:: 1] oner_neq0.
Proof.
rewrite polyC1.
apply poly_inj.
rewrite polyseq1 //.
Qed.

Lemma polyC': forall (c: R) (H: is_true (c != 0)), c%:P = @Polynomial R [:: c] H.
Proof.
intros.
apply poly_inj.
unlock polyC. rewrite /insubd /poly_nil /odflt /oapp /insub.
destruct idP; auto.
simpl in n. contradiction.
Qed.

Lemma polyC0': 0%:P = @Polynomial R [:: ] oner_neq0.
Proof.
rewrite polyC0.
rewrite -polynil_eq.
apply poly_inj; auto.
Qed.

Lemma polyX': 'X = @Polynomial R [:: 0; 1] oner_neq0.
Proof.
intros.
unlock polyX; destruct polyX_key; rewrite /polyX_def  /=.
unlock cons_poly;
rewrite ?polyC0' ?polyC1' //.
Qed.

Lemma polyX2': 'X * 'X = @Polynomial R [:: 0; 0; 1] oner_neq0.
Proof.
intros.
apply poly_inj.
rewrite polyseqMX.
rewrite  /= polyX' //.
rewrite polyX_eq0 //.
Qed.

Lemma polyX3': 'X * ('X * 'X) = @Polynomial R [:: 0; 0; 0; 1] oner_neq0.
Proof.
intros.
apply poly_inj.
rewrite polyX2'.
rewrite mulrC polyseqMX //.
rewrite /Algebra.zero /= /eq_op /= polyseqC eq_refl //.
Qed.

Lemma polyX4': 'X * ('X * ('X * 'X)) = @Polynomial R [:: 0; 0; 0; 0; 1] oner_neq0.
Proof.
intros.
apply poly_inj.
rewrite polyX3'.
rewrite mulrC polyseqMX //.
rewrite /Algebra.zero /= /eq_op /= polyseqC eq_refl //.
Qed.

Lemma polyX5': 'X * ('X * ('X * ('X * 'X))) = @Polynomial R [:: 0; 0; 0; 0; 0; 1] oner_neq0.
Proof.
intros.
apply poly_inj.
rewrite polyX4'.
rewrite mulrC polyseqMX //.
rewrite /Algebra.zero /= /eq_op /= polyseqC eq_refl //.
Qed.

Lemma polyX6': 'X * ('X * ('X * ('X * ('X * 'X)))) = @Polynomial R [:: 0; 0; 0; 0; 0; 0; 1] oner_neq0.
Proof.
intros.
apply poly_inj.
rewrite polyX5'.
rewrite mulrC polyseqMX //.
rewrite /Algebra.zero /= /eq_op /= polyseqC eq_refl //.
Qed.

Lemma polyX7': 'X * ('X * ('X * ('X * ('X * ('X * 'X))))) = @Polynomial R [:: 0; 0; 0; 0; 0; 0; 0; 1] oner_neq0.
Proof.
intros.
apply poly_inj.
rewrite polyX6'.
rewrite mulrC polyseqMX //.
rewrite /Algebra.zero /= /eq_op /= polyseqC eq_refl //.
Qed.

Lemma polyX8': 'X * ('X * ('X * ('X * ('X * ('X * ('X * 'X)))))) = @Polynomial R [:: 0; 0; 0; 0; 0; 0; 0; 0; 1] oner_neq0.
Proof.
intros.
apply poly_inj.
rewrite polyX7'.
rewrite mulrC polyseqMX //.
rewrite /Algebra.zero /= /eq_op /= polyseqC eq_refl //.
Qed.

Definition integ (p: {poly R}) : {poly R} := cons_poly 0 (\poly_(i < (size p)) (p`_i / ((S i)%:R))).

Lemma deriv_integ: forall p: {poly R}, deriv (integ p) = p.
Proof.
move => [s H].
rewrite /integ /deriv /=.
apply poly_inj.
destruct (size s) eqn:H0.
-
destruct s; try discriminate H0. clear H0.
rewrite /= poly0 size_cons_poly nil_poly ?eq_refl /= poly0 polyseq0 //.
-
assert (H7: is_true (s`_n != 0))
 by (rewrite (last_nth Algebra.zero) H0 in H; auto).
rewrite size_cons_poly H0 /nilp size_poly_eq.
2:{  rewrite ?prednK; try Lia.lia. simpl. 
revert H7.
set d := s`_n. clearbody d.
apply contraNN.
intro.
rewrite mulIr_eq0 in H1; auto.
intros ? ? ?.
set (u := natmul _ _) in H1. 
assert (u > 0)%R by apply ltr0Sn.
clearbody u.
assert (x1 / u * u = x2 / u * u)%R. f_equal; auto.
rewrite -!mulrA in H3.
rewrite mulVf ?mulr1 in H3; auto.
apply lt0r_neq0; auto.
}
simpl.
apply (@eq_from_nth _ 0).
rewrite size_poly_eq //. 
simpl. 
rewrite coef_cons. simpl.
rewrite coefE ltnSn.
clear - H7; rewrite mulrn_eq0 /= mulf_eq0 negb_or H7 /= invr_neq0 //.
intros.
rewrite size_poly_eq in H1.
2: rewrite coef_cons /= coefE ltnSn mulrn_eq0 /= mulf_eq0 negb_or H7 /= invr_neq0 //.
rewrite coefE H1 coef_cons /= coefE H1 -mulrnAr -mulr_natr mulVr ?mulr1 //.
rewrite unitfE mulrn_eq0 /=  oner_eq0 //.
Qed.

Lemma derivable_oo_LRcontinuous_horner: forall P lo hi, @derivable_oo_LRcontinuous R _ (horner P) lo hi.
Proof.
intros.
split.
- intros ? ?. apply derivable_horner.
- exact/cvg_at_right_filter/continuous_horner.
- exact/cvg_at_left_filter/continuous_horner.
Qed.

Lemma Rintegral_poly: forall lo hi (lo_lt_hi: lo<hi)
  (P: polynomial (reals_Real__to__GRing_NzSemiRing R)),
eq
  (Rintegral (reverse_coercion (lebesgue_measure_lebesgue_measure__canonical__measure_function_Measure R) (@lebesgue_measure R))
     (mkset
        (fun x : Order.POrder.sort (reals_Real__to__Order_POrder R) =>
         is_true (in_mem x (mem (Interval (BSide true lo) (BSide false hi))))))
     (fun x : Measurable.sort (measurable_structure_g_sigma_algebraType__canonical__measurable_structure_Measurable measurable) =>
      horner P x))
 (GRing.add (horner (integ P) hi) (opp (horner (integ P) lo))).
Proof.
intros.
rewrite /Rintegral (@continuous_FTC2 R (horner P) (horner (integ P)) lo hi lo_lt_hi).
- reflexivity.
- apply derivable_within_continuous; intros ? ?; apply derivable_horner.
- apply derivable_oo_LRcontinuous_horner.
-  intros ? ?. 
rewrite -derivE. rewrite deriv_integ //.
Qed.

Lemma bounded_range (T : Type) (K : realFieldType) (V : pseudoMetricNormedZmodType K) (f : T -> V) (A : set T) : 
   [bounded f x | x in A] <-> bounded_set (f @` A)%classic.
Proof.
split; intro.
-
simpl.
destruct H.
exists x. destruct H; split; auto.
intros. simpl in *. intros.
destruct H2.
subst x1.
apply H0; auto.
-
simpl in *.
destruct H.
exists x.
destruct H; split; auto.
intros. simpl in *; intros.
eapply H0 in H1.
apply H1.
eexists; eauto.
Qed.

Lemma within_compact_continuous_bounded (T : topologicalType) (V : normedModType R) (A : set T) (f : T -> V) :
  compact A -> {within A, continuous f}%classic -> [bounded f x | x in A].
Proof.
  move=> cA cf.
  apply/bounded_range.
  apply: compact_bounded.
  by apply: continuous_compact.
Qed.


Lemma in_within_continuous: forall (a b: Real.sort R) (f: Real.sort R -> Real.sort R),
   {in `[a, b]%classic, continuous f } ->
  {within `[a, b], continuous f}%classic.
Proof.
intros.
pose proof  @continuous_subspace_itv R `[a,b]  f.
unfold from_subspace.
apply H0.
clear - H.
replace (mem (mkset _)) with (mem (Interval (BSide true a) (BSide false b))) in H; auto.
unfold mem; simpl. f_equal.
extensionality x.
unfold in_mem. simpl.
unfold in_set, mkset.
rewrite boolp.asboolb //.
Qed.

Lemma continuous_bounded: forall (a b: Real.sort R) (f: Real.sort R -> Real.sort R),
    {in `[a, b], continuous f}%classic ->
    [bounded f x | x in `[a,b]].
Proof.
intros.
set i := `[a,b]%classic.
apply  (within_compact_continuous_bounded _ _ i f).
apply segment_compact.
apply in_within_continuous; auto.
Qed.

Lemma continuousM' : forall (a b: Real.sort R) (f g: Real.sort R -> Real.sort R),
 {in `[a, b]%classic, continuous f} ->
 {in `[a, b]%classic, continuous g} ->
  {in `[a, b]%classic, continuous (GRing.mul_fun f  g)}.
Proof.
intros.
hnf in H, H0.
hnf; intros.
pose proof @continuousM R _ f g x.
rewrite !forE in H2.
apply H2; auto.
Qed.

Lemma within_continuous_measurable_fun:
 forall (a b: Real.sort R) (f: Real.sort R -> Real.sort R),
   is_true (a < b) ->
   {within `[a, b], continuous f}%classic ->
   measurable_fun `[a, b] f.
Proof.
intros * Hab H.
rewrite continuous_within_itvP in H; auto.
destruct H.
eapply measurable_fun_itv_cc with (b0:=false) (b1:=true).
apply open_continuous_measurable_fun; auto.
clear - H.
simpl in *.
replace (mem (mkset _)) with (mem (Interval (BSide false a) (BSide true b))); auto.
unfold mem; simpl. f_equal.
extensionality x.
unfold in_mem. simpl.
unfold in_set, mkset.
rewrite boolp.asboolb //.
Qed.

Lemma in_continuous_measurable_fun:
 forall (a b: Real.sort R) (f: Real.sort R -> Real.sort R),
   is_true (a < b) ->
   {in `[a, b], continuous f}%classic ->
   measurable_fun `[a, b] f.
Proof.
intros * Hab H.
apply within_continuous_measurable_fun; auto.
apply in_within_continuous; auto.
Qed.


Lemma in_continuous_cst: forall (i: set (Order.POrder.sort (reals_Real__to__Order_POrder R))) (c: R),
   {in i, continuous (fun _:  R =>c)}.
Proof.
intros.
hnf; intros.
apply @cst_continuous.
Qed.

Lemma in_continuousN: forall (i: set (Order.POrder.sort (reals_Real__to__Order_POrder R))) (f: R -> R),
   {in i, continuous f} ->
   {in i, continuous (\- f)}.
Proof.
intros.
hnf; intros.
apply @continuousN.
rewrite forE. apply H; auto.
Qed.

Lemma in_continuousB: forall (i: set (Order.POrder.sort (reals_Real__to__Order_POrder R)))  (f g: R -> R),
   {in i, continuous f} ->
   {in i, continuous g} ->
   {in i, continuous (f \- g)}.
Proof.
intros; hnf; intros.
apply @continuousB; rewrite forE; auto.
Qed.

Lemma in_continuousD: forall (i: set (Order.POrder.sort (reals_Real__to__Order_POrder R))) (f g: R -> R),
   {in i, continuous f} ->
   {in i, continuous g} ->
   {in i, continuous (f \+ g)}.
Proof.
intros; hnf; intros.
apply @continuousD; rewrite forE; auto.
Qed.

Lemma in_continuousM: forall (i: set (Order.POrder.sort (reals_Real__to__Order_POrder R)))  (f g: R -> R),
   {in i, continuous f} ->
   {in i, continuous g} ->
   {in i, continuous (f \* g)}.
Proof.
intros; hnf; intros.
apply @continuousM; rewrite forE; auto.
Qed.

Lemma in_continuous_horner: forall (i: set (Order.POrder.sort (reals_Real__to__Order_POrder R))) (f: {poly R}),   {in i, continuous (horner f)}.
Proof.
intros * ? ? ?. apply continuous_horner.
Qed.

End R.

Hint Resolve in_continuous_cst in_continuous_horner in_continuousN in_continuousB in_continuousD in_continuousM : continuous.

End Rewriting.

Import Rewriting.

Lemma size_polyseq_coeffs': forall {T} (p: {poly T}) (n: nat),
  (forall i,  (n < i)%N -> (coefp i p == 0)) -> 
     (size p <=n.+1)%N.
Proof.
move => T [p Hp] n H.
simpl in *.
revert Hp n H; induction p; simpl; intros; auto.
assert (last 1 p != 0). {
 clear - Hp. induction p; simpl; auto. apply oner_neq0.
}
specialize (IHp H0 n.-1).
destruct n.
-
simpl in *.
clear - H H0.
rewrite (last_nth 0) in H0.
specialize (H (size p)). simpl in H0.
destruct (size p); auto.
simpl in H, H0.
specialize (H erefl).
move :H => /eqP => H. rewrite H in H0. rewrite eq_refl in H0. discriminate.
-
simpl in *.
assert (size p <= n.+1)%N; [ | Lia.lia].
apply IHp.
intros. apply (H (S i)). Lia.lia.
Qed.

Lemma size_polyseq_coeffs: forall {T} (p: {poly T}) (n: nat),
  (forall i,  (n <= i)%N -> (coefp i p == 0)) -> 
     (size p <=n)%N.
Proof.
intros.
destruct n.
-
destruct p as [p Hp]. simpl in *.
rewrite (last_nth 0) in Hp.
specialize (H (size p).-1).
simpl in *.
destruct (size p); auto.
simpl in *.
specialize (H erefl).
move :H => /eqP => H. rewrite H in Hp. rewrite eq_refl in Hp; discriminate.
-
apply size_polyseq_coeffs'; auto.
Qed.

(* end details *)

(* begin details:  Lemmas and tactics copied from matrix_util.v *)
Lemma size_ord_enum: forall n, size (ord_enum n) = n.
Proof.
intros.
pose proof val_ord_enum n.
simpl in H.
transitivity (size (iota 0 n)).
transitivity (size (map (nat_of_ord (n:=n)) (ord_enum n))).
rewrite size_map; auto.
f_equal; auto.
apply size_iota.
Qed.


Lemma nth_ord_enum': forall n (d i: 'I_n), nth d (ord_enum n) i = i.
Proof.
intros.
pose proof (val_ord_enum n).
simpl in H.
apply ord_inj.
pose proof ltn_ord i.
rewrite <- nth_map with (x2:=nat_of_ord d).
rewrite H. rewrite nth_iota. Lia.lia. Lia.lia.
rewrite size_ord_enum.
auto.
Qed.

Lemma nth_List_nth: forall {A: Type} (d: A) (l: seq.seq A) (n: nat),
  seq.nth d l n = List.nth n l d.
Proof.
  move => A d l. elim : l => [//= n | //= h t IH n].
  - by case : n.
  - case: n. by []. move => n. by rewrite /= IH.
Qed.

Lemma ord_enum_cases: forall [n] (P: 'I_n -> Prop),
  List.Forall P (ord_enum n) ->
  forall i, P i.
Proof.
intros.
rewrite List.Forall_forall in H.
apply H.
clear.
pose proof @nth_ord_enum' n i i.
rewrite nth_List_nth in H.
rewrite <- H.
apply List.nth_In.
change @length with @size.
rewrite size_ord_enum.
pose proof (ltn_ord i); Lia.lia.
Qed. 

Lemma index_enum_ord_enum: forall n: nat, 
   index_enum (fintype_ordinal__canonical__fintype_Finite n) = ord_enum n.
Proof.
intros.
unfold index_enum.
rewrite locked_withE.
rewrite Finite.enum.unlock.
simpl.
auto.
Qed.

Ltac is_ground_nat n := lazymatch n with O => idtac | S ?n' => is_ground_nat n' end.

Ltac compute_ord_enum n := 
  tryif is_ground_nat n then idtac 
      else  fail "compute_ord_enum: Need a ground term natural number, but got" n; 
  pattern (ord_enum n); 
  match goal with |- ?F _ => 
    let f := fresh "f" in set (f:=F);
      let c := constr:(ord_enum n) in let d :=  eval compute in c in change (f d);
      let e := fresh "e" in repeat (destruct ssrbool.idP as [e|e];
        [ replace e with ssrbool.isT by apply eq_irrelevance; clear e | try (contradiction e; reflexivity)]);
     subst f
  end.

Ltac ord_enum_cases j :=
 lazymatch type of j with ordinal ?n => 
  pattern j; 
  apply ord_enum_cases;
  compute_ord_enum n
 end;
 repeat apply List.Forall_cons; try apply List.Forall_nil;
 clear j.

Ltac expand_bigop :=
 match goal with |- context [bigop.body _ (index_enum (fintype_ordinal__canonical__fintype_Finite ?n))] =>
 let B := fresh "B" in 
 set B := bigop.body _ _ _; pattern B; subst B; 
 lazymatch goal with |- ?b _ => set B := b end;
rewrite bigop.unlock index_enum_ord_enum;
 compute_ord_enum n;
 try rewrite ?/reducebig ?/foldr ?/applybig;
  repeat change (comp ?A ?B ?C) with (A (B C));
 cbv beta match;
 repeat change (nat_of_ord (@Ordinal _ ?a _)) with a;
 simpl nth;
 subst B; cbv beta
end.


Definition append1fun [n][T] (f: 'I_n -> T) (x: T) (i:  'I_(n.+1)) : T.
rewrite -addn1 in i.
destruct (split i) as [i' | i'].
apply (f i').
apply x.
Defined.

Lemma append1fun_last: forall [n][T] (f: 'I_n -> T) (x: T) (n': 'I_n.+1), nat_of_ord n' = n -> append1fun f x n' = x.
Proof.
intros.
rewrite /append1fun /eq_rect /eq_rec.
destruct n'. simpl in *.
subst m.
destruct (addn1 n).
unfold split. destruct ltnP; auto.
simpl in i0.
Lia.lia.
Qed.

Lemma append1fun_notlast:  forall [n][T] (f: 'I_n -> T) (x: T) i j, nat_of_ord i = 
         nat_of_ord j -> append1fun f x i = f j.
Proof.
intros.
rewrite /append1fun /eq_rect /eq_rec.
destruct (addn1 n).
unfold split. destruct ltnP; auto. f_equal. apply ord_inj; auto.
rewrite H in i0.
pose proof (ltn_ord j).
Lia.lia.
Qed.

Lemma Rintegral_gt_0: 
forall {R : realType} (a b: R) (h : Real.sort R -> Real.sort R), 
   {in `[a, b]%classic, continuous h} ->
   {in `[a, b]%classic, forall x, is_true (0 <= h x)} ->
  ~ {in `[a, b]%classic, forall x, is_true (h x == 0)} ->
    (0 <  \int[lebesgue_measure]_(x in `[a, b])  h x).
Proof.
Admitted.

(* end details *)

(** Now, on with the show.  The [Context] command parameterizes the whole development
  by any construction of the real numbers. *)

Section R.
Context {R : realType}.

(** This derivation follows Lecture 23 of _Afternotes on Numerical Analysis_ 
    by G. W. Stewart, SIAM Press, 1996.  Henceforth Stewart will be in Roman font
  _and your humble Editor will write in Italics.  -- Andrew Appel_. *)

(** _All the definitions and theorem-statements from Stewart are formalized
  in Rocq, but many of the theorems are Admitted, not proved.  However,
  all the theorems (below) for the specific application to Legendre polynomials
  are proved_. *)

(** ** Gaussian quadrature: The Setting *)

(** 1. The Gauss formula we will actually derive has the form,

      [  ∫_a ^b f(x) w(x) dx ≅ A_0 f(x_0) + A_1 f(x_1) + ⋯ + A_n f(x_n)   ]

  where w(x) is a weight function that is greater than zero on the interval [[a,b]].

   2. The incorporation of a weight function creates no complications in the theory.
  However, it makes our integrals, which are already too long, even more cumbersome.
 Since the interval [[a,b]] and the weight w(x) do not change, we will suppress them along with
 the variable of integration and write, 
    ∫ f =  [  ∫_a^b f(x) w(x) dx  ].
*)

Section Integral.
 Variable (a b : R).
 Variable Hab: a<b.
 Variable w: R -> R.
 Variable wpos: forall x, a <= x <= b -> w x > 0.
 Variable wcontinuous:     {in `[a, b], continuous w}%classic.
 Definition  intgal (f: R -> R) := 
            \int[lebesgue_measure]_(x in `[a,b]%classic) (f x * w x).
 Notation "∫" := intgal.
 
 Hint Resolve wcontinuous: continuous.
 Lemma wmeasurable: measurable_fun `[a, b] w.
Proof. apply in_continuous_measurable_fun; auto with continuous. Qed.

(*
 Definition bounded (f: R -> R) := exists M: R,  forall x, a <= x <= b -> Num.norm (f x) <= M.
*)

(** 3.  Regarded as an operator on functions, ∫  is linear.  That is, 

         ∫ α f = α ∫  f and ∫ (f + g) = ∫ f + ∫ g.  

     We will make extensive use of linearity in what follows. *)

 Lemma intgal_linear1: forall (α: R) (f:  R->R),
      {in `[a, b], continuous f}%classic ->
      ∫ (α \*: f) = α * ∫ f.
Proof.
intros * CONT.
unfold intgal.
match goal with |- eq (@Rintegral ?d ?T R ?c ?s _) _ => 
   pose proof @RintegralZl d T R c s (fun x => f x * w x) α end.
set g := fun x => mul _ _.
set h := fun x => mul α _ in H.
replace g with h.
2:{ clear H. subst g h. extensionality x. rewrite /scale_fun /scale mulrA //. }
apply H; clear g h H.
-
apply measurable_itv.
-
apply measurable_bounded_integrable.
+
apply measurable_itv.
+
rewrite /= lebesgue_measure_itv /=  (_: Order.lt (EFin a) (EFin b) = (a<b)) // Hab. 
rewrite /GRing.add /= /adde /Order.lt /= /has_quality /= /in_mem /=. lra.
+
simpl.
apply measurable_funM; [ | apply wmeasurable].
apply in_continuous_measurable_fun; auto.
+
apply continuous_bounded; auto.
apply continuousM'; auto.
Qed.

 Lemma intgal_linear2: forall (f g: R -> R), 
      {in `[a, b], continuous f}%classic ->
      {in `[a, b], continuous g}%classic ->
      ∫ (f \+ g) = ∫ f + ∫ g.
Proof.
intros * Hf Hg.
unfold intgal.
match goal with |- eq (@Rintegral ?d ?T R ?c ?s _) _ => 
   pose  proof @RintegralD d T R c s (mul_fun f w) (mul_fun g w)
end.
set u := fun x => mul _ _.
set v := fun x => add _ _ in H.
replace u with v.
2: extensionality y; subst u v; rewrite /= mulrDl //.
apply H; clear H u v.
+
apply measurable_itv.
+
rewrite /=.
apply continuous_compact_integrable.
apply segment_compact.
pose proof continuousM' a b _ _  Hf wcontinuous.
apply in_within_continuous; auto.
+
rewrite /=.
apply continuous_compact_integrable.
apply segment_compact.
pose proof continuousM' a b _ _  Hg wcontinuous.
apply in_within_continuous; auto.
Qed.

(** ** Orthogonal polynomials *)

(** 4.  Two functions f and g are said to be _orthogonal_ if ∫  f g = 0.

  The term "orthogonal" derives from the fact that the integral ∫  f g can be regarded as an inner product
  of f and g.  Thus two polynomials are orthogonal if their inner product is zero, which is the usual definition
  of orthogonality in R^n. *)


 Definition orthogonal (f g: R -> R) := ∫ (f \* g) = 0.

(**  5. A sequence of  _orthogonal polynomials_ is a sequence {p_i},  i={0,1,...,∞} of polynomials
   with deg(p_i) = i such that      i ≠ j -> ∫ p_i p_j = 0.                         (23.1)

  _Editor's note: the [size] of a polynomial is the degree plus 1_.
*)

 Definition orthogonal_polynomials (p: nat -> {poly R}) : Prop := 
   (forall i, size (p i) = i.+1) /\
   (forall i j: nat, i<>j ->  orthogonal (horner (p i)) (horner (p j))).

(** Since orthogality is not altered by multiplication by a nonzero constant, we
   may normalize the polynomial p_i so that the coefficient of x^i is one: i.e.,

   p_i(x) = x^i + a_{i,i-1}x^{i-1} + ⋯ + a_{i0}.

 Such a polynomial is said to be _monic_.  *)

Locate monic_pred.  (*  Constant mathcomp.algebra.poly.monic_pred *)
Print monic_pred.  (* = fun [R] (p : {poly R}) => lead_coef p == 1 *)

(** 6. Our immediate goal is to establish the existence of orthogonal polynomials.
  Although we could, in principle, determine the coefficients [a_{ij}] of [p_i] in the
  natural basis by using the orthogonality conditions (23.1), we get better results by
  expressing [p_{n+1}] in terms of lower-order orthogonal polynomals.  To do this
  we need the following general result.
    ------------------------------------------------------------------------------------------------
   Let \{p_i\}_{i=0}^∞ be a sequence of (monic) polynomials such that p_i is exactly of
   degree i. If

       q(x) = a_n x^n + a_{n-1} x^{n-1} + ⋯ + a_0                   (23.2)

  then q can be written uniquely in the form

       q = b_n p_n + b_{n-1} p_{n-1} + ⋯ + b_0 p_0.               (23.3)
*)


Section P.

  Variable  (p: nat -> {poly R}).
  Variable p_degree: forall i, size (p i) = i.+1%N.
  Variable p_monic: forall i, monic_pred (p i).

  Lemma stewart_lemma_23_6:
      forall (n: nat) (q: {poly R}), 
        (size q <= n.+1)%N ->
        { b: 'I_n.+1 -> R  |  q = \sum_(i<n.+1) (polyC(b i) * p i)}.

(** 7.  In establishing this result, we may assume that the polynomials [ p_i ] are monic.
  The proof is by induction.  For n=0 we have,

      [ q(x) = a_0 = a_0 ⋅ 1 = a_0 p_0(x) ].

   Hence we must have [ b_0 = a_0 ].

     Now assume that q has the form (23.2).  Since [ p_n ] is the only polynomial in
    the sequence [ p_n, p_{n-1}, ⋯, p_0 ] that contains x^n and since [ p_n ] is monic, it follows
    that we must have [ b_n = a_n ].  Then the polynomial [ q-a_n p_n ] is of degree n-1.
    Hence by the induction hypothesis, it can be expressed uniquely in the form

           [  q - a_n p_n = b_{n-1} p_{n-1} + ⋯ + b_0 p_0 ],

    which establishes the result.
*)

Proof.
clear w wpos wcontinuous a b Hab.
induction n; intros.
-
destruct q as [q Hq].
simpl in H.
change (0+1)%N with 1%N in H.
simpl in q.
destruct q as [ | a0 [ | ] ].
+
exists (fun _ => 0).
expand_bigop.
rewrite ?r_ring.
apply poly_inj. simpl. rewrite /GRing.zero /= polyC0' //.
+
exists (fun _ => a0).
expand_bigop.
move :(p_degree 0) (p_monic 0) => H0 H1.
destruct (p 0) as [p0 Hp0].
simpl in H0,H1.
destruct p0; [ discriminate H0 | ].
destruct p0; [ | discriminate H0].
clear H.
unfold lead_coef in H1.
simpl in H1.
rewrite ?r_ring.
rewrite -?polyC'. 
rewrite (eqP H1).
ring.
+
simpl in H. Lia.lia.
-
 pose q' : {poly R} := q - (q`_n.+1)%:P * p n.+1.
 destruct (IHn q') as [b Hb]; clear IHn. {
   replace (n+1)%N with n.+1 by Lia.lia.
   apply /leq_sizeP.
   intros.
   subst q'.
   rewrite coefB mul_polyC coefZ.
   move :(p_degree n.+1) (p_monic n.+1) => /= Hd Hm.
   destruct (j == n.+1) eqn:H1.
   - change (is_true (j == n.+1)) in H1. 
   move :H1 => /eqP H1. subst j.
   move :Hm. rewrite lead_coefE Hd /=.
   move /eqP => Hm. rewrite Hm mulr1.
   ring.
  -   
  rewrite (@nth_default _ _ (polyseq (p n.+1))); [ | rewrite Hd; Lia.lia].
  rewrite mulr0 subr0.
  rewrite nth_default //.
  assert (j != n.+1). rewrite H1 //.
  clear - H2 H0 H.
  set s := size (polyseq q) in H|-*. clearbody s.
  Lia.lia.
 }
 subst q'. simpl in Hb.
 set u := _ * _ in Hb. set v := bigop.body _ _ _ in Hb. 
 assert (q = u + v). rewrite -Hb. ring. clear Hb. subst u v.
 exists (append1fun b (q`_n.+1)).
 set bn := q`_n.+1 in H0|-*. clearbody bn.
 clear H.
 rewrite big_mknat big_nat_rev /= big_ltn //.
 rewrite big_nat_rev /=. rewrite big_add1 /=.
 subst q.
 rewrite ?inordK; try Lia.lia.
 f_equal.
 rewrite append1fun_last // inordK; Lia.lia.
 rewrite big_mknat.
  rewrite ?big_nat.
   apply eq_big; auto.
  move => i Hi /=.
 rewrite ?inordK; try Lia.lia.
 f_equal.
2: f_equal; Lia.lia.
  set j := (0 + _ - _ )%N.
 replace j with i by Lia.lia. clear j.
 erewrite append1fun_notlast. reflexivity.
 rewrite ?inordK; try Lia.lia.
Qed.
  

(** 8.  A consequence of this result is the following.
            The polynomial [ p_{n+1} ] is orthogonal to any polynomial q of degree n or less.

      For from (23.3) it follows that

            [ ∫  p_{n+1} q = b_n ∫  p_{n+1} p_n + ⋯ + b_0 ∫  p_{n+2}p_0 = 0 ],

      the last equality following from the orthogonality of the polynomials [p_i].


       _(Note: [p_{n+2}p_0] sic in original, but surely p_{n+1}p_0 is meant.)_
*)


Lemma horner_sum' :
forall [R : nzSemiRingType] [I : Type] (r : seq I) (P : pred I)
  (F : I -> {poly R}),
 horner (\sum_(i <- r | P i) F i) = fun x => \sum_(i <- r | P i) (horner (F i) x).
Proof.
intros.
extensionality x.
apply horner_sum.
Qed.


Lemma intgal_sum: forall [T] (r: seq T) (F: T -> R -> R), 
 (\big[and/Logic.True]_(i <- r)  {in `[a, b]%classic, continuous (F i)}) ->
  ∫ (fun x => \sum_(i <- r) F i x) = \sum_(i <- r)  ∫ (F i).
Proof.
intros.
transitivity (intgal (foldr (fun i => add_fun (F i)) (fun=>0) r)).
-
f_equal.
extensionality x.
rewrite !bigop.unlock /reducebig /comp /applybig.
set y := Algebra.zero. clearbody y.  revert y; clear; induction r; simpl; intros; f_equal; auto.
-
transitivity (foldr (fun i:T => add (intgal (F i))) Algebra.zero r); [ | rewrite !bigop.unlock //].
set z := {1}Algebra.zero.
set u := Algebra.zero.
assert  (∫ (fun=> z) = u). {
 subst u z.
replace (fun=> _) with (0 \*: (fun _ : R => 0:R)).
2: extensionality x; rewrite /scale_fun /scale /= mul0r //.
rewrite intgal_linear1. ring.
apply in_continuous_cst.
}
 clearbody z; clearbody u.
revert z u H0; induction r; simpl; intros; auto.
rewrite big_cons in H. destruct H.
rewrite intgal_linear2; auto. f_equal; auto.
clear - H1.
induction r.
apply in_continuous_cst.
rewrite big_cons in H1. destruct H1.
apply in_continuousD; auto.
Qed.


Definition orthogonal_polynomials_upto (n: nat) (p: nat -> {poly R}) : Prop := 
   (forall i, size (p i) = i.+1) /\
   (forall i j: nat, (i<j<=n)%N ->  orthogonal (horner (p i)) (horner (p j))).

Lemma polySn_orthogonal_n: 
       forall n,
         orthogonal_polynomials_upto n.+1 p ->
         forall (q: {poly R}), 
            (size q <= n.+1)%nat ->
            orthogonal (horner (p n.+1)) (horner q).
Proof.
intros.
destruct (stewart_lemma_23_6 n q H0) as [d H1].
red.
subst.
rewrite -hornerM'.
transitivity (∫ (horner (\sum_(i < n.+1) (d i)%:P * (p n.+1 * p i)))).
-
f_equal.
f_equal.
rewrite mulr_sumr.
apply eq_big; auto.
intros i _.
rewrite mulrC -mulrA (mulrC (p i)) //.
-
rewrite horner_sum'.
simpl.
rewrite intgal_sum.
2:{ clear; induction (index_enum _). rewrite big_nil. auto. rewrite big_cons. split; auto. apply in_continuous_horner.
}
transitivity (\sum_(i<n.+1) (0:R)).
apply eq_big; auto.
intros i _.
rewrite hornerM'.
rewrite hornerC'.
rewrite intgal_linear1.
2: apply in_continuous_horner.
rewrite hornerM'.
destruct H.
rewrite mul_funC.
rewrite /orthogonal in H1. rewrite H1.
ring.
pose proof ltn_ord i; Lia.lia.
rewrite sumr_const.
ring.
Qed.

End P.

(** 9. To establish the existence of orthogonal polynomials, we begin by computing
    the first two.  Since [p_0] is monic and of degree zero,

                [  p_0(x) ≡ 1.   ]

      Since [p_1] is monic and of degree one, it must have the form

                [   p_1(x) = x - α_1.    ]

    To determine [α_1], we use orthogonality:

           [    0 = ∫  p_1 p_0 = ∫  (x-α_1)⋅1  = ∫  x - α_1 ∫ 1.    ]

    Since the function 1 is positive in the interval of integration,  ∫ 1 > 0, and it 
    follows that

           [              α_1 = (∫ x) / (∫ 1).   ]

     10.  In general we will seek [ p_{n+1} ]  in the form

        [  p_{n+1} = x p_n - α_{n+1} p_n - β_{n+1} p_{n-1} - γ_{n+1} p_{n-2} - ⋯ . ]

      As in the construction of [p_1], we use orthogonality to determine the coefficients

      [ α_{n+1}, β_{n+1}, γ_{n+1}, ⋯ ]

          To determine [ α_{n+1} ], write

      [ 0 = ∫  p_{n+1} p_n = ∫  x p_n p_n - α_{n+1} ∫ p_n p_n - β_{n+1} ∫  p_{n-1} p_n - γ_{n+1} ∫ p_{n-2} p_n - ⋯ . ]

      By orthogonality, [ 0 = ∫ p_{n-1} p_n = ∫  p_{n-2} p_n = ⋯ ] .   Hence

            [  ∫  x p_n^2 - α_{n+1} ∫ p_n^2 = 0. ]

      Since [ ∫  p_n^2 > 0 ] , we may solve this equation to get

            [   α_{n+1} = ∫ x p_n^2  /  ∫  p_n^2. ]

      For [ β_{n+1} ], write

           [ 0 = ∫ p_{n+1} p_{n-1} = ∫ x p_n p_{n-1} - α_{n+1} ∫ p_n p_{n-1} - β_{n+1} ∫ p_{n-1} p_{n-1} - γ_{n+1} ∫ p_{n-2} p_{n-1} - ⋯ ] .

     Dropping terms that are zero because of orthogonality, we get

                   [   ∫ x p_n p_{n-1} - β_{n+1} ∫ p_{n-1}^2 = 0  ]
      or [ β_{n+1} = (∫ x p_n p_{n-1} ) / (∫ p_{n-1}^2).  ]

     11. The formulas for the remaining coefficients are similar to the formula for [ β_{k+1} ]; e.g.,

                [  γ_{n+1} = (∫  x p_n p_{n-2}) / (∫  p_{n-2}^2)  ].

        However, there is a surprise here.  The denominator [[sic]]   [ x p_n p_{n-2} ] can be written
        in the form [∫  x p_{n-2} p_n].  Since [x p_{n-2}] is of degree n-1 it is orthogonal to [p_n];
        i.e.,  [∫ x p_{n-2} p_{n-1 [sic]}   = 0].  Hence [γ_{k+1} = 0], and likewise the coefficients of
         [p_{n-3}, p_{n-4}, ⋯] are zero.

     12.  To summarize:
          The orthogonal polynomials can be generated by the following recurrence:

          -      [p_0 = 1,]
          -      [p_1 = x - α_1,]
          -      [p_{n+1} = x p_n - α_{n+1} p_n - β_{n+1} p_{n-1},               n=1,2,⋯,]
         where 

                 [ α_{n+1} = (∫  x p_n^2) / (∫ p_n^2)]   and [β_{n+1} =  (∫  x p_n p_{n-1}) / (∫  p_{n-1}^2)]. 

          The first two equations in the recurrence merely start things off.  The right-hand side
          of the third equation  contains three terms and for that reason is called the
          _three-term recurrence_ for the orthogonal polynomials.
*)

Fixpoint three_term_recurrence (n: nat) : {poly R} * {poly R} :=
   match n with
   | 0 => (1%:P, 0%:P)
   | 1 => let α1 :=  ∫ id /  ∫ (fun=>1) in ('X - α1%:P, 1%:P)
            (* the 1 case is not quite subsumed by the S n' case, because
                there would be an unfortunate division by zero in the computation of βn. *)
   | S n' => let (pn', pn'') := three_term_recurrence n'
                   in let αn :=  ∫ (id \* (horner pn' \* horner pn')) / ∫(horner pn' \* horner pn')
                   in let βn := ∫ (id \* (horner pn' \* horner pn'')) / ∫(horner pn'' \* horner pn'')
                   in ('X * pn' - scale_poly αn pn' - scale_poly βn pn'', pn')
  end.

Definition ortho_p n := fst (three_term_recurrence n).

Lemma ortho_p_prev: forall n,  (three_term_recurrence n.+1).2 = (three_term_recurrence n).1.
Proof.
intros.
simpl.
destruct n; auto.
destruct (three_term_recurrence n.+1); auto.
Qed.

Lemma ortho_p_size: forall n,  size (ortho_p n) = n.+1.
Proof.
assert (forall n i, (i < n)%N -> size (ortho_p i) = i.+1); [ | intros; apply (H n.+1); auto].
rewrite /ortho_p.
induction n; intros. Lia.lia.
destruct i;  rewrite /= ?size_poly1 //.
assert (Hi := IHn i ltac:(Lia.lia)).
destruct (three_term_recurrence i) eqn:H3; simpl in *.
assert (Hlead: lead_coef p != 0). {
  rewrite lead_coefE.
  clear - Hi.
  destruct p as [p Hp].
  simpl in *. rewrite nth_last. destruct p; try discriminate. simpl in *. auto.
}
destruct i. {
   simpl. rewrite size_polyDl. apply size_polyX. rewrite size_polyN.
   rewrite size_polyC size_polyX. Lia.lia.
}
set u := _ / _. clearbody u.
set v := _ / _. clearbody v.
assert ((size (- scale_poly u p) < size ('X * p)%R)%N). {
  rewrite size_polyN scale_polyE.
  apply leq_trans with ((size (polyC u) + size p).-1.+1); [ apply size_polyMleq | ].
  rewrite size_proper_mul.
  rewrite size_polyC size_polyX Hi.  Lia.lia.
  rewrite lead_coefX mul1r //.
}
rewrite ?size_polyDl //.
-
rewrite size_proper_mul.
rewrite Hi size_polyX. Lia.lia.
rewrite lead_coefX mul1r //.
-
rewrite size_polyN scale_polyE.
apply leq_trans with ((size (polyC v) + size p0).-1.+1); [ apply size_polyMleq | ].
rewrite size_proper_mul.
rewrite size_polyC Hi size_polyX.
assert (p0 = (three_term_recurrence i.+1.-1).1). {
 rewrite -ortho_p_prev. simpl Nat.pred. rewrite H3 //.
}
rewrite H1. rewrite IHn. Lia.lia. Lia.lia.
rewrite lead_coefX mul1r //.
Qed.

Lemma ortho_p_monic: forall n, monic_pred (ortho_p n).
Proof.
rewrite /ortho_p.
induction n; simpl.
rewrite lead_coef1 //.
destruct (three_term_recurrence n) eqn:H3.
pose proof (ortho_p_size n). rewrite /ortho_p H3 /= in H.
simpl in *.
destruct n. {
  rewrite lead_coefDl. rewrite lead_coefX //. rewrite size_polyN size_polyC size_polyX; Lia.lia.
}
set u := _ / _. clearbody u.
set v := _ / _. clearbody v.
rewrite ?lead_coefDl.
*
rewrite lead_coefM lead_coefX mul1r //.
*
rewrite size_polyN scale_polyE.
apply leq_trans with ((size (polyC u) + size p).-1.+1); [ apply size_polyMleq | ].
rewrite size_proper_mul ?H.
rewrite size_polyC size_polyX.  Lia.lia.
rewrite lead_coefX mul1r //.
move :IHn => /eqP H0. rewrite H0. apply oner_neq0.
*
rewrite size_polyN scale_polyE.
apply leq_trans with ((size (polyC v) + size p0).-1.+1); [ apply size_polyMleq | ].
rewrite size_polyDl.
rewrite size_proper_mul.
rewrite size_polyC  size_polyX H.
assert (p0 = (three_term_recurrence n.+1.-1).1). {
 rewrite -ortho_p_prev. simpl Nat.pred. rewrite H3 //.
}
simpl Nat.pred in H0. subst p0. rewrite ortho_p_size. Lia.lia.
rewrite lead_coefX mul1r //.
move :IHn => /eqP Hi. rewrite Hi. apply oner_neq0.
rewrite size_polyN scale_polyE.
apply leq_trans with ((size (polyC u) + size p).-1.+1); [ apply size_polyMleq | ].
rewrite ?size_proper_mul ?H.
rewrite size_polyC size_polyX. Lia.lia.
rewrite lead_coefX mul1r.
move :IHn => /eqP H0. rewrite H0. apply oner_neq0.
Qed.

Lemma ortho_p_nonzero: forall n, ortho_p n != 0.
Proof.
intro.
move :(ortho_p_monic n).
rewrite /monic_pred.
rewrite -(lead_coef_eq0 (ortho_p n)).
set c := lead_coef _. clearbody c.
move => H0.
assert (@eq R c 1). lra. subst.
apply @oner_neq0.
Qed.


Lemma sqr_poly_positive: forall p: {poly R}, p != 0 ->  ∫ (horner (p * p)) > 0.
Proof.
intros.
pose n := size p.
assert (0 < n)%N by (rewrite -size_poly_eq0 in H; Lia.lia).
assert (~ (forall x, a <= x <= b -> horner (p * p) x = 0)). {
intro.
pose rs := map (fun i => a + (b-a)/(n+n+1)%:R * i%:R) (iota 1 (n+n)). 
assert (is_true (size rs < size (polyseq (p * p)))%N). {
apply max_poly_roots.
-
rewrite - size_poly_eq0 size_proper_mul. change (size p) with n. Lia.lia.
rewrite -lead_coef_eq0 in H. apply mulf_neq0; auto.
-
rewrite {}/rs.
set f := _ * _ in H1|-*.
clearbody f. clearbody n. clear p H.
rewrite all_map.
rewrite /preim.
apply (@sub_all _ [pred i | (0 < i < n+n+1)%N]).
+
simpl.
intros i ?. simpl in H. simpl.
rewrite rootE. rewrite H1 //.
rewrite -mulrA.
assert (0 < (n + n + 1)%:R^-1 * i%:R :> R). {
apply mulr_gt0.
rewrite invr_gt0 ltr0n. Lia.lia.
rewrite ltr0n. Lia.lia.
}
assert ((n + n + 1)%:R^-1 * i%:R < 1 :> R). {
rewrite ltr_pdivrMl ?mulr1.
rewrite ltr_nat. Lia.lia.
rewrite ltr0n. Lia.lia.
}
set c :=  ((n + n + 1)%:R^-1 * i%:R)  in H3,H2|-*.
assert (0 < (b-a)*c < b-a). {
red; rewrite Bool.andb_true_iff; split; change (?A = true) with (is_true A); try nra.
apply mulr_gt0; try lra.
rewrite subr_gt0 //.
rewrite gtr_pMr; auto.
rewrite subr_gt0 //.
}
lra.
+
set lo := S O.
set k := (n+n)%nat.
clearbody k. 
clearbody lo.
revert lo; induction k; simpl; intros; auto.
specialize (IHk (lo.+1)).
red; rewrite Bool.andb_true_iff; split; change (?A = true) with (is_true A).
Lia.lia.
replace (k.+1+lo)%N with (k+lo.+1)%N by Lia.lia.
revert IHk.
apply sub_all.
intro; simpl; intro. Lia.lia.
-
rewrite /rs.
pose proof (iota_uniq 1 (n+n)).
rewrite map_inj_uniq //.
hnf; intros.
assert (0 <  (b - a) / (n + n + 1)%:R)%R.
apply divr_gt0.
rewrite subr_gt0 //.
rewrite ltr0n. Lia.lia.
set c := _ / _ in H4,H3.
clearbody c.
simpl in *.
apply /eqP. rewrite -(@eqr_nat R) /=. apply /eqP. nra.
}
rewrite size_proper_mul in H2; [ | rewrite -lead_coef_eq0 in H; apply mulf_neq0; auto].
fold n in H2.
subst rs.
rewrite size_map in H2.
rewrite size_iota in H2. Lia.lia.
}
assert (forall x, 0 <= horner (p * p) x). {
intros. rewrite hornerM.
nra.
}
set g := horner (p * p) in H1,H2|-*.
assert ( {in `[a, b]%classic, continuous g}).
rewrite /g; auto with continuous.
clearbody g. simpl in g.
rewrite /∫.
set h := fun x => g x * w x.
assert {in `[a, b]%classic, continuous h}.
apply continuousM'; auto.
assert (forall x,  is_true (a <= x <= b) ->  is_true (0 <= h x)).
intros. rewrite /h. apply mulr_ge0; auto.
assert (~ (forall x : Order.Preorder.sort (reals_Real__to__Order_Preorder R), is_true (a <= x <= b) -> h x = 0)).
contradict H1.
intros.
specialize (H1 _ H6).
rewrite /h in H1.
pose proof (wpos _ H6).
assert (g x * w x == 0) by lra.
rewrite mulIr_eq0 in H8.
lra; auto.
apply /rregP.
lra.
clearbody h.
simpl in *.
assert (
  prop_in1
    (mem (mkset (fun x : Real.sort R => is_true (in_mem x (mem (Interval (BSide true a) (BSide false b)))))))
    (inPhantom (forall x : Real.sort R, 0 <= h x))). {
intro; intros. apply H5.
rewrite /in_mem /=  /in_set /=  /pred_of_itv /= boolp.asboolb in H7.
apply H7.
}
assert (~ {in `[a, b]%classic, forall x : Real.sort R, is_true (h x == 0)}). {
contradict H6. intros. apply /eqP. apply H6.
rewrite /in_mem /=  /in_set /=  /pred_of_itv /= boolp.asboolb //.
}
apply Rintegral_gt_0; auto.
Qed.

Lemma ortho_p2_positive: forall n,  ∫ (horner (ortho_p n * ortho_p n)) > 0.
Proof.
intros. apply sqr_poly_positive. apply ortho_p_nonzero.
Qed.

Lemma ortho_p_orthogonal_special': 
   forall n i, (i < n)%N -> orthogonal (horner (ortho_p i.+1)) (horner (ortho_p i)).
Proof.
induction n; intros; [Lia.lia | ].
red.
rewrite -hornerM'.
rewrite {1}/ortho_p.
simpl.
destruct i.
-
rewrite /ortho_p /= r_ring.
move :(ortho_p2_positive 0).
rewrite /ortho_p /= mul1r.
rewrite hornerC' => H1.
set α1 := _ / _.
rewrite hornerD' intgal_linear2; auto with continuous.
rewrite /α1.
rewrite hornerX'.
rewrite -(mulr1 (opp _)).
rewrite hornerM'.
rewrite hornerN' hornerC'.
rewrite intgal_linear1; auto with continuous.
rewrite mulrC.
rewrite mulrN.
rewrite hornerC'.
field.
lra.
-
destruct (three_term_recurrence i.+1) as [p p0] eqn:Hp.
simpl.
assert (p = ortho_p i.+1) by (rewrite /ortho_p Hp //); subst p.
assert (p0 = ortho_p i) by (rewrite /ortho_p -ortho_p_prev Hp //); subst p0.
clear Hp.
rewrite ?mulrDl.
rewrite ?hornerD'.
rewrite ?intgal_linear2; auto with continuous.
rewrite ?scale_polyE.
rewrite -?mulNr.
rewrite -?polyCN.
rewrite -?mulrA.
rewrite (hornerM' (polyC _)).
rewrite hornerC'.
rewrite intgal_linear1; auto with continuous.
rewrite (hornerM' (polyC _)).
rewrite hornerC'.
rewrite intgal_linear1; auto with continuous.
assert (Pi := ortho_p2_positive i).
assert (Pi1 := ortho_p2_positive i.+1).
rewrite -?(hornerM' (ortho_p i)).
rewrite -?(hornerM' (ortho_p i.+1)).
set c :=  ∫ (horner (ortho_p i * ortho_p i)) in Pi|-*.
set d :=   ∫ (horner (ortho_p i.+1 * ortho_p i.+1)) in Pi1|-*.
rewrite (hornerM' 'X) hornerX'.
set e := ∫ (id \* _).
assert (- (e/d) * d = -e) by (field; lra).
rewrite {}H0.
replace (e-e)%R with (0:R) by (field; lra).
rewrite add0r.
rewrite (mulrC (ortho_p i)).
rewrite hornerM'.
rewrite (IHn i ltac:(Lia.lia)) mulr0 //.
Qed.

Lemma ortho_p_orthogonal_special: 
   forall n, orthogonal (horner (ortho_p n.+1)) (horner (ortho_p n)).
Proof.
intros. apply (ortho_p_orthogonal_special' n.+1). Lia.lia.
Qed.

Lemma ortho_p_orthogonal': 
   forall n i j, (i < j <= n)%N -> orthogonal (horner (ortho_p j)) (horner (ortho_p i)).
Proof.
induction n; intros; [ Lia.lia | ].
destruct j; [ Lia.lia | ].
assert (i=j \/ i<j)%N by Lia.lia.
destruct H0; [subst j ; apply ortho_p_orthogonal_special | ].
assert (i < j <=n)%N by Lia.lia.
clear H H0.
rewrite {1}/ortho_p.
simpl.
destruct (three_term_recurrence j) eqn:H3.
red.
rewrite -hornerM'.
assert (H7: ∫ (fun=> 1) != 0). {
  replace (∫ (fun=>1)) with (∫ (horner (ortho_p 0 * ortho_p 0))).
  pose proof (ortho_p2_positive 0). set c := ∫ _ in H|-*. clearbody c. clear H3 p p0 H1. lra.
  f_equal. rewrite /ortho_p /= mulr1 hornerC' //.
}
destruct j; [Lia.lia | ].
simpl.
assert (p = ortho_p j.+1) by (rewrite /ortho_p H3 //); subst p.
assert (p0 = ortho_p j) by (rewrite /ortho_p -ortho_p_prev H3 //); subst p0.
clear H3.
move :(ortho_p2_positive j.+1) => Pj1.
move :(ortho_p2_positive j) => Pj.
rewrite -?hornerM'.
set c1 := ∫ (horner (ortho_p j.+1 * ortho_p j.+1)) in Pj1|-*.
set c := ∫ (horner (ortho_p j * ortho_p j)) in Pj|-*.
rewrite ?mulrDl.
rewrite ?hornerD'.
rewrite ?intgal_linear2; auto with continuous.
rewrite ?scale_polyE.
rewrite -?mulNr.
rewrite -?mulrA.
rewrite -?polyCN.
rewrite ?(hornerM' (polyC _)).
rewrite ?hornerC'.
rewrite ?intgal_linear1; auto with continuous.
rewrite ?hornerM'.
assert (i=j \/ i<j)%N by Lia.lia.
destruct H.
-
subst i.
rewrite -?hornerM'.
change (∫(horner (ortho_p j * ortho_p j))) with c.
rewrite hornerM' hornerX'.
set u := ∫ (id \* horner (ortho_p j.+1 * ortho_p j)).
rewrite (_:  (- (u / c) * c) = -u :> R); [ | field; lra].
rewrite (hornerM' _ (ortho_p j)).
rewrite (IHn j j.+1); [ | Lia.lia].
rewrite mulr0.
ring.
-
assert (H2: (i < j < n)%N) by Lia.lia. clear H1 H.
rewrite (IHn i j); [ | Lia.lia].
rewrite mulr0.
rewrite (IHn i j.+1); [ | Lia.lia].
rewrite mulr0.
rewrite ?addr0.
rewrite -?hornerM'.
rewrite (mulrC (ortho_p j.+1)).
rewrite mulrA.
assert (SIZEi := ortho_p_size i).
assert (SIZExi : size ('X * ortho_p i) = i.+2). {
rewrite mulrC. rewrite size_mulX. Lia.lia.
apply (@contraFneq _ false); [ | auto]. intro.
pose proof (ortho_p_size i). rewrite H in H0.
rewrite size_poly0 in H0. discriminate H0.
}
pose proof polySn_orthogonal_n ortho_p ortho_p_size ortho_p_monic j.
assert (  orthogonal_polynomials_upto j.+1 ortho_p ). {
split. apply ortho_p_size. intros. red. rewrite mul_funC. apply IHn. Lia.lia.
}
specialize (H H0). clear H0.
rewrite mulrC.
rewrite hornerM'.
apply H.
rewrite SIZExi. 
Lia.lia.
Qed.

Lemma ortho_p_orthogonal: 
   forall i j, (i < j)%N -> orthogonal (horner (ortho_p j)) (horner (ortho_p i)).
Proof.
intros. apply (ortho_p_orthogonal' j); Lia.lia.
Qed.

(** ** Zeros of orthogonal polynomials *)

(** 13.  It will turn out that the abscissas of our Gaussian quadrature formula will
        be the zeros of [p_{n+1}].  We will now show that 
        
         The zeros of [p_{n+1}] are real, simple, and lie in the interval [[a,b]].

     14.  Let [x_0, x_1, ⋯, x_k]  be the zeros of odd multiplicity of [p_{n+1}] in [[a,b];] i.e.,
         [x_0, x_1, ⋯, x_k] are the points at which [p_{n+1}] changes sign in [[a,b]].  If k=n, we are 
         through, since the [x_i] are the n+1 zeros of [p_{n+1}].

               Suppose then that k<n and consider the polynomial

                    [   q(x) = (x-x_0)(x-x_1)⋯(x-x_k)  ].

        Since deg(q) = k+1 < n+1, by orthogonality

                    [  ∫ p_{n+1} q = 0  ].

        On the other hand, [p_{n+1}(x) q(x)] cannot change sign on [[a,b]] -- each sign change
        in [p_{n+1}(x)] is cancelled by a corresponding sign change in q(x).  It follows that

                    [ ∫ p_{n+1} q <> 0 ],

         which is a contradiction.
*)

(** _Editor's note: The following predicate [roots_of_ortho_p] says that [roots] is 
     a list of n distinct values, all of which evaluate (under the polynomial) to zero, 
    which implies that they are simple roots_.*)

Record roots_of_ortho_p (n: nat) := {
  ROOTS_vals: n.-tuple R;
  ROOTS_zero: all (root (ortho_p n)) (tval ROOTS_vals);
  ROOTS_sorted: sorted Order.lt (tval ROOTS_vals);
  ROOTS_inrange: all (fun x => a <= x <= b) (tval ROOTS_vals)
}.
Arguments ROOTS_vals [n].
Arguments ROOTS_zero [n].
Arguments ROOTS_sorted [n].
Arguments ROOTS_inrange [n].

(** _Editor's note: the statement "14.  . . . are the n+1 zeros of [p_{n+1}]" implicitly claims that 
     there are at most n+1 zeros.  That is any zero of the polynomial is already in the roots list,
     which is explicitly an n.-tuple_.  Therefore: *)

Lemma roots_of_ortho_p_at_most: forall [n] (roots: roots_of_ortho_p n),
  forall x, root (ortho_p n) x -> x \in ROOTS_vals roots.
Proof.
intros.
destruct (x \in ROOTS_vals roots) eqn:?H; auto.
pose proof @max_poly_roots _ (ortho_p n) (x :: ROOTS_vals roots) (ortho_p_nonzero n).
change (size (cons ?A ?B)) with (size B).+1 in H1.
replace (size (ROOTS_vals roots)) with n in H1.
2: destruct (ROOTS_vals roots); simpl; Lia.lia.
rewrite ortho_p_size in H1.
assert (n.+1 < n.+1)%N; [ | Lia.lia].
apply H1; clear H1.
simpl.
change (@root _) with (@root R).
destruct (root (ortho_p n) x); try discriminate.
simpl.
apply ROOTS_zero.
rewrite cons_uniq.
rewrite H0.
simpl.
pose proof (ROOTS_sorted roots).
apply lt_sorted_uniq in H1.
auto.
Qed.

Lemma same_members_increasing_equal: 
 forall (al1 : seq (Real.sort R)) (Hs1 : is_true (sorted <%R al1))
          (al2 : seq (Real.sort R)) (Hs2 : is_true (sorted <%R al2))
      (H : forall x : Real.sort R, is_true (x \in al1) <-> is_true (x \in al2)),
  al1 = al2.
Proof.
clear.
intros.
 rewrite /in_mem /= in H.
 revert al2 Hs2 H; induction al1; destruct al2; simpl in *; intros; auto.
 specialize (H s). rewrite eq_refl /= in H.
 destruct H as [_ H]. specialize (H ltac:(auto)). discriminate.
 specialize (H a). rewrite eq_refl /= in H.
 destruct H as [H _]. specialize (H ltac:(auto)). discriminate.
 specialize (IHal1 (path_sorted Hs1) _ (path_sorted Hs2)).
 destruct (eq_op s a) eqn:?H.
 - assert (s=a) by (apply /eqP; auto). subst s. clear H0.
  f_equal. apply IHal1. intros. specialize (H x). destruct (eq_op x a) eqn:?H.
 +  assert (x=a) by (apply /eqP; auto). subst x. clear H H0 IHal1.
    apply order_path_min in Hs1; [ | intros ? ? ?; lra].
    apply order_path_min in Hs2; [ | intros ? ? ?; lra].
   assert (mem_seq al1 a = false). {
     induction al1; simpl; auto. simpl in Hs1. rewrite IHal1. lra.
     destruct (a<a0); auto.
  } rewrite {}H.
   assert (mem_seq al2 a = false). {
     induction al2; simpl; auto. simpl in Hs2. rewrite IHal2. lra.
     destruct (a<a0); auto.
  } rewrite {}H.
  tauto.
 + simpl in H. auto.
- pose proof (H s). rewrite H0 eq_refl in H1. simpl in H1.
  exfalso.
  destruct H1 as [_ H1]. specialize (H1 ltac:(auto)).
   assert (s < a \/ a < s) by lra; clear H0.
  destruct H2.
 + clear - H0 H1 Hs1.
    apply order_path_min in Hs1; [ | intros ? ? ?; lra].
    induction al1; simpl in *. discriminate. 
     assert ((s == a0) = false) by lra. rewrite H /= in H1. 
     apply IHal1; auto.  destruct (a<a0); auto.
  +  pose proof (H a).
     assert (a != s). clear H2 H1 H Hs2 IHal1. lra. destruct (a==s); try discriminate; simpl in *.
     rewrite eq_refl /= in H2. pose proof (proj1 H2 ltac:(auto)).
     clear - H0 H4 Hs2.
    apply order_path_min in Hs2; [ | intros ? ? ?; lra].
    induction al2; simpl in *. discriminate. 
     assert ((a == a0) = false) by lra. rewrite H /= in H4. 
     apply IHal2; auto.  destruct (s<a0); auto.
Qed.
 
Lemma roots_of_ortho_p_unique (n: nat) : forall r r' : roots_of_ortho_p n, r=r'.
Proof.
move => r r'.
move :(roots_of_ortho_p_at_most r) => J1.
move :(roots_of_ortho_p_at_most r') => J2.
destruct r as [v1 Hz1 Hs1 Hin1].
destruct r' as [v2 Hz2 Hs2 Hin2].
simpl in J1, J2.
assert (forall x, x \in v1 <-> x \in v2). {
 intros; split; intro.
 + apply J2; move :Hz1; move  /allP => A1. apply A1; auto.
 + apply J1; move :Hz2; move /allP => A2; apply A2; auto.
}
assert (v1 = v2). {
clear - H Hs1 Hs2.
 apply tuple_ext.
 rewrite ?memtE in H.
 apply same_members_increasing_equal; auto.
}
subst v1.
f_equal; apply eq_irrelevance.
Qed.

(** _Editor's note:   Stewart's derivation talks about "THE roots" of the polynomial, as if
  they constructively exist.  Well, indeed they do exist, but_:
  - We want concretely presented roots in a simple form that we can calculate with, AND
  - Mathcomp-Analysis does not yet have proof that a polynomial can be factored into n roots, AND
  - Mathcomp-Analysis especially does not have a CONSTRUCTIVE such proof, AND
  - Even a constructive proof would not be useful unless it presented the roots in a simple
       form that we could calculate with.

  _Therefore we will do it slightly differently.  For the polynomials of interest, we will present
   the roots explicitly, and prove that they are indeed roots and are indeed distinct.  That
   is, we will present instances of the package [roots_of_ortho_p]_. *)

(** ** Gaussian quadrature *)

(** 15.  The Gaussian quadrature formula is obtained by constructing a Newton-Cotes
     formula on the zeros of the orthogonal polynomial [p_{n+1}].

     Let [x0, x_1, ⋯, x_n] be the zeros of the orthogonal polynomial [p_{n+1}] and set

              [ A_i = ∫  L_i,   i = 0, 1, ⋯, n, ]

     where [L_i ] is the ith Lagrange polynomial over [x_0, x_1, ⋯, x_n].  For any function f let

              [ G_n f = A_0 f(x_0) + A_1 f(x_1) + ⋯ + A_n f(x_n) ].

    Then  [ deg(f) ≤ 2n+1  ⇒  ∫  f = G_n f ].
*)

 Section Quadrature.
  Variable n : nat.
  Variable roots: roots_of_ortho_p n.
  Definition zeros_of_ortho_p := tval (ROOTS_vals roots).


  (** _Editor's note: When manipulating Lagrange polynomials in MathComp, we
     will need to prove that the numbers [x_0, x_1, ..., x_{n-1}] are distinct.  That is,
    MathComp's lagrangeE lemma requires injectivity over (fun i => x_i).  In this case, 
    the sequence x is the zeros_of_ortho_p, so we need to prove that function is injective.
    Unfortunately, lagrangeE stupidly requires injectivity over all the natural numbers,
    not just  over the [0..n-1] that index the roots list.  So we need this [extend_roots] 
    function to make that work_. *)
  Definition extend_roots  (i: nat) : R :=
     nth ((i+1)%:R+b) zeros_of_ortho_p i.

   Lemma extend_roots_injective: injective extend_roots.
   (* begin details: Proof. ... Qed. *)
   Proof.
    pose proof ROOTS_inrange roots.
    pose proof ROOTS_sorted roots.
    rewrite /extend_roots /zeros_of_ortho_p.
    set rl := tval (ROOTS_vals roots) in H,H0|-*. clearbody rl.
    simpl in H.
    assert (is_true (all (fun x => x <= b) rl)).
    eapply sub_all; [ | apply H].  intros ? ?. lra. clear H. rename H1 into H.
    intros i j H1.
    assert (is_true (i < size rl) \/ is_true (i >= size rl))%N by Lia.lia.
    assert (is_true (j < size rl) \/ is_true (j >= size rl))%N by Lia.lia.
    destruct H2 as [Hi|Hi];  destruct H3 as [Hj|Hj].
    -
     assert ((i < j)%N \/ i=j \/ (j<i)%N) by Lia.lia.
     destruct H2 as [? |[?|?]]; auto.
     rewrite <- (sorted_ij rl i j ((i + 1)%:R + b)%E ((j + 1)%:R + b)%E H0 Hi Hj) in H2.
     rewrite H1 in H2. apply lt_nsym in H2; auto; contradiction.
     rewrite <- (sorted_ij rl j i ((j + 1)%:R + b)%E ((i + 1)%:R + b)%E H0 Hj Hi) in H2.
     rewrite H1 in H2. apply lt_nsym in H2; auto; contradiction.
   - 
    pose proof (@all_nthP _  (fun x => x  <= b)  rl ((i + 1)%:R + b)%E). rewrite H in H2. inversion H2.
    apply H3 in Hi.
    rewrite H1 in Hi. clear H2 H3.
    rewrite nth_default in Hi; auto.
    assert ((j+1)%:R <= 0%:R) by lra.
    rewrite ler_nat in H2. Lia.lia.
   - 
    pose proof (@all_nthP _  (fun x => x  <= b)  rl ((j + 1)%:R + b)%E). rewrite H in H2. inversion H2.
    apply H3 in Hj.
    rewrite -H1 in Hj. clear H2 H3.
    rewrite nth_default in Hj; auto.
    assert ((i+1)%:R <= 0%:R) by lra.
    rewrite ler_nat in H2. Lia.lia.
   -
    rewrite ?nth_default in H1; auto.
    assert ((j+1)%:R == (i+1)%:R) by lra.
    rewrite eqr_nat in H2. Lia.lia.
  Qed.
(* end details *)

  Definition L : n.-tuple {poly_n R} := lagrange n extend_roots.
  Definition gauss_weight (i: 'I_n) := ∫ (horner (tnth L i)).

  Definition G (f: R->R) := \sum_(i<n) (gauss_weight i * (f (tnth zeros_of_ortho_p i))).

  (** 16.  To establish this result, first note that by construction the integration formula
    [G_n f] is exact for polynomials of degree less than or equal to n (see section 21.17).

         Now let deg(f) ≤ 2n+1.  Divide f by [p_{n+1}] to get

                 [ f = p_{n+1}q + r],      deg(q), deg(r) ≤ n.                             (23.4)

      Then

       - [G_n f = Σ_i A_i f(x_i)]
       -          = [Σ_i A_i(p_{n+1}(x_i)q(x_i) + r(x_i))]                       (by 23.4)
       -          = [Σ_i A_i r(x_i)]                                                 because p_{n+1}(x_i)=0
       -          = [G_n r]
       -          = [∫ r]                                                because [G_n] is exact for deg(r) ≤ n
       -          = [∫ (p_{n+1}q+r)]                            because [∫ p_{n+1}q = 0] for deg(q) ≤ n
       -          = ∫ f                                                (by 23.4).
      Quot erat demonstrandum.
  *)
 End Quadrature.
 
 (** 21.17  [from chapter 21].  Let x0, x1, ..., xn be points in the interval [a,b]. (In point of fact,
        the points do not have to lie in the interval, and sometimes they don't.  But mostly they do.)
        Then we wish to determine constants A0, A1, ... An such that,

       [ deg(f) ≤ n ⇒ ∫_a^b f(x) dx = A0 f(x0) + A1 f(x1) + . . . + An f(xn) . ]       (21.5)

       This problem has an elegant solution in terms of Lagrange polynomials:
    
        Let Li be the ith Lagrange polynomial over x0,x1,...,xn.  Then

        [ Ai = ∫_a^b Li(x) dx ]       (21.6)
 
        are the unique coefficients satisfying (21.5).

      21.18  To prove the assertion first note that the rule must integrate the ith 
          Lagrange polynomial.  Hence

        [ ∫_a^b Li(x) = Σ_{j=0}^n Aj Lj(xj) = Ai Li(xi) = Ai, 

       which says that the only possible for the Ai is given by (21.6).

        Now let deg(f) ≤ n.  Then

       [ f(x) = Σ_{i=0}^n f(xi) . ]

        Hence

        [ ∫_a^b Lj(x)dx = Σ_{i=0}^n f(xi) ∫_a^b Li(x)dx = Σ_{i=0}^n f(xi)Ai ]

       which is just (21.5).

 *)

 Lemma extend_rootsE: forall [n] (roots: roots_of_ortho_p n) (i: 'I_n),
     extend_roots n roots (nat_of_ord i) = tnth (ROOTS_vals roots) i.
Proof.
 intros.
 rewrite /extend_roots /tnth.
  apply set_nth_default.  rewrite /zeros_of_ortho_p size_tuple; apply ltn_ord.
Qed.

  Lemma quadrature_exact_upto_n:
      forall [n] roots (f: {poly R}), (size f <= n.+1)%N -> ∫ (horner f) = G n.+1 roots (horner f).
Proof. 
  intros.
  rewrite /G.
  pose proof @lagrange_gen R n.+1 (extend_roots _ roots) erefl (extend_roots_injective _ _) f H.
  rewrite {}H0. rewrite horner_sum' intgal_sum.
 2:{ clear; induction (index_enum _). rewrite big_nil. auto. rewrite big_cons. split; auto. apply in_continuous_horner.
  }
 apply eq_big; auto; intros.
 set F := horner _.
 rewrite (_: (fun x => F x)=F).
  2: extensionality x; auto.
 subst F.
 rewrite hornerM' hornerC' intgal_linear1; auto with continuous.
 rewrite /gauss_weight /L. rewrite mulrC. f_equal.
 transitivity (\sum_j (f.[tnth (ROOTS_vals roots) j] * (i==j)%:R)).
 2:{ 
  rewrite big_mkcond_idem. 2: simpl; lra. simpl.
  apply eq_big; auto; intros.
  rewrite {1}/extend_roots.
  set u :=  nth _ _ _.
  replace u with (tnth (zeros_of_ortho_p n.+1 roots) i0).
  2:{ apply set_nth_default.  rewrite /zeros_of_ortho_p size_tuple; apply ltn_ord. }
  clear u.
  rewrite /zeros_of_ortho_p.
  rewrite hornerM. rewrite hornerC.
  f_equal.
  symmetry. rewrite eq_sym.
  rewrite -(@lagrange_sample R n.+1 (extend_roots n.+1 roots) erefl (extend_roots_injective _ _) i0 i).
  f_equal.
 rewrite extend_rootsE //. 
 }
 transitivity ( \sum_j (if j==i then f.[extend_roots n.+1 roots j] else 0)).
  rewrite -big_mkcond_idem. 2: simpl; lra. simpl.
  rewrite big_pred1_eq_id. lra.
  apply eq_big; auto; intros. rewrite eq_sym. simpl. destruct (_ == _); simpl; try lra.
  rewrite mulr1. f_equal. apply extend_rootsE.
Qed.

  (* Back to paragraph 23.16 *)

From mathcomp Require Import polydiv. Import Pdiv.CommonRing.

  Lemma quadrature_exact_for': 
      forall [n] (roots : roots_of_ortho_p n.+1) (f: {poly R}), 
            (size f <= 2*n+2)%N ->  ∫ (horner f) = G n.+1 roots (horner f).
Proof.
 intros.
 move :(divp_eq f (ortho_p n.+1)) => H0.
 move :(@size_divp _ f (ortho_p n.+1) (ortho_p_nonzero _)); rewrite ortho_p_size => SIZEq.
 move :(@ltn_modpN0 _ f (ortho_p n.+1) (ortho_p_nonzero _)); rewrite ortho_p_size => SIZEr.
 set q := (f %/ ortho_p n.+1) in H0 SIZEq. clearbody q.
 set r := (f %% ortho_p n.+1) in H0 SIZEr. clearbody r.
 rewrite /G H0.
 symmetry.
 transitivity  (\sum_i gauss_weight n.+1 roots i * r.[tnth (zeros_of_ortho_p n.+1 roots) i]). {
    apply eq_big; auto => /= i _. f_equal.
    rewrite hornerD hornerM.
    rewrite -{2}(add0r(horner r _)). f_equal.
    rewrite -(mulr0 (horner q (tnth (zeros_of_ortho_p n.+1 roots) i))). f_equal.
    rewrite /zeros_of_ortho_p.
    apply /rootP.
    apply /all_tnthP.
    apply ROOTS_zero.
}
 rewrite -/(G n.+1 roots (horner r)).
 rewrite -quadrature_exact_upto_n ; [ | set j := size r in SIZEr|-*; clearbody j; Lia.lia].
 rewrite hornerD'  intgal_linear2; auto with continuous.
 rewrite mulrC. rewrite hornerM'.
 rewrite polySn_orthogonal_n.
 2: exact ortho_p_size. 2: exact ortho_p_monic.
 3:{
 assert (size q == 0 \/ size q > 0)%N by Lia.lia.
 destruct H1. move :H1 => /eqP H2. rewrite H2; auto.
  rewrite size_poly_gt0 in H1.
  rewrite SIZEq. set j := size f in H|-*. Lia.lia.
 }
 2:{ split. exact ortho_p_size. intros. red. rewrite mul_funC. apply ortho_p_orthogonal. Lia.lia. }
 lra.
Qed.

  Lemma quadrature_exact_for: 
      forall [n] (roots : roots_of_ortho_p n)  (f: {poly R}), (size f <= 2*n)%N ->  ∫ (horner f) = G n roots (horner f).
Proof.
destruct n.
+ intros. assert (size f == 0)%N by Lia.lia. rewrite size_poly_eq0 in H0.
   move :H0 => /eqP H0; subst f.
   rewrite -(mulr0 (polyC 0)) hornerM' /G big_ord0 hornerC'. 
   rewrite intgal_linear1; auto with continuous. rewrite mul0r //.
+ rewrite (_: 2*n.+1 =  2*n+2)%N;[ | Lia.lia]. exact (@quadrature_exact_for' n).
Qed.

(** 17. An important corollary of these results is that the coefficients [A_i] are positive.
       To see this note that

               [ L_i(x_j) = L_i^2(x_j) = if i=j then 1 else 0 ]. 

      Since [ L_i^2(x) ≥ 0] and [deg(L_i^2) = 2n],

             [  0 < ∫ L_i^2 = Σ_j A_i L_i^2(x_j) = A_i ].
*)
   Lemma gauss_weight_positive: forall [n] roots i, gauss_weight n roots i > 0.
   Proof.
    intros.
    destruct n; [destruct i; Lia.lia |].
    pose proof @lagrange_sample R n.+1 (extend_roots n.+1 roots) ltac:(Lia.lia) (extend_roots_injective _ roots).
    fold (L _ roots) in H.
    assert (size (tnth (L n.+1 roots) i) = n.+1)
      by (apply size_lagrange_; [reflexivity | apply extend_roots_injective]).
   assert ( tnth (L n.+1 roots) i != 0 ). {
      rewrite /L.
      apply /eqP. intro. rewrite H1 in H0. rewrite size_poly0 in H0. discriminate.
  }
    pose proof sqr_poly_positive (tnth (L n.+1 roots) i) H1.
   rewrite (quadrature_exact_for roots) in H2.
    2:{ set u := tnth _ _ in H0,H1|-*. clearbody u.
        rewrite size_proper_mul. Lia.lia.
         pose proof (lead_coef_eq0 u). set z := u==0 in H2. change ((lead_coef u == 0) = z) in H2.
         change (_ == _) with z in H1. rewrite -H2 in H1.
         apply mulf_neq0; auto.
    }
   set u := G _ _ _ in H2.
   rewrite (_: gauss_weight n.+1 roots i = u); auto; subst u; clear H2.
   rewrite /G.
   transitivity (\sum_(j<n.+1) (gauss_weight n.+1 roots j * (j==i)%:R)).
   2:{ apply eq_big; auto. intros j _. rewrite hornerM. rewrite /L.
        rewrite /L in H. rewrite (eq_sym j i).
        replace (tnth _ j) with (extend_roots n.+1 roots j).
        2:{ rewrite /extend_roots. rewrite /tnth. apply set_nth_default.
             rewrite /zeros_of_ortho_p size_tuple. apply ltn_ord.
        }
      rewrite H. f_equal. destruct (i==j); simpl; try lra.
  }
  clear H H0 H1.
  set f := gauss_weight _ _. clearbody f. simpl in f.
  transitivity (\sum_(j<n.+1) if (j==i) then f j else 0).
  2: apply eq_big; auto; intros; destruct (_ == _); simpl; lra.  
  rewrite -big_mkcond_idem. 2: simpl; lra.
  rewrite big_pred1_eq_id. simpl; lra.
Qed.

(** 18.  Since [ A_0 + A_1 + ⋯ + A_n = ∫ 1 ], no coefficient can be larger than 1.  Consequently,
     we cannot have a situation in which large coefficients create large intermediate results
      that suffer cancellation when they are added. *)


   Lemma gauss_weight_leq_1:  forall [n] roots i, gauss_weight n roots i <= ∫ (horner 1).
   Proof.
   intros.
    destruct n. destruct i. Lia.lia.
    rewrite (@quadrature_exact_for _ roots).
    2: rewrite size_poly1; Lia.lia.
    rewrite /G. rewrite hornerC' -mulr_suml mulr1.
    replace (gauss_weight n.+1 roots i) with (\sum_j (if (j==i) then gauss_weight n.+1 roots j else 0)).
    apply ler_sum. intros. destruct (i0==i); auto. pose proof (gauss_weight_positive roots i0). lra.
    rewrite -big_mkcond_idem. simpl. 2: simpl; lra.
  rewrite big_pred1_eq_id. simpl; lra.
 Qed.

(** ** Error and convergence *)

(** 19.  Gaussian quadrature has error formulas similar to the ones for Newton-Cotes
    formulas.  Specifically

        [  ∫  f - G_n f =  ( f^(2n+2)(ξ) / (2n+2)!) ∫ p_{n+1}^2 ],

     where ξ ∈ [[a,b]]. *)
  Lemma quadrature_error: forall n roots (f: R->R),
      exists ξ:R, a <= ξ <= b /\
       ∫ f - G n roots f =  
       derive1n (2*n+2) f ξ /
        (factorial(2*n+2))%:R * ∫ (fun x => (horner (ortho_p(n.+1)) x)^2).
  Admitted.

(** 20. A consequence of the positivity of the coefficients A_i is that Gaussian
    quadrature converges for any continuous function; that is,

       [ f continuous ⇒ \lim_{n→∞} G_n f = ∫ f ].

    The proof -- it is a good exercise in elementary analysis -- is based on the Weierstrass
    approximation theorem, which says that for any continuous function f
    there is a sequence of polynomials that converges uniformly to f.
*)

(*  TODO: fix the "roots"  parameter of G
  Lemma quadrature_converges:  forall (f: Real.sort R -> Real.sort R) (x: R),
    (forall x, continuous_at x f) -> limn (fun n => G n roots f) = ∫ f.
  Abort.  (* Provable I'm sure, but it's not clear that we need it. *)
*)

End Integral.
End R.
(** ** Examples *)

(** 21. Particular Gauss formulas arise from particular choices of the interval [[a,b]]
      and the weight function w(x).  The workhorse is Gauss-Legendre quadrature,
     in which [[a,b]] = [[-1,1]] and w(x)=1, so that the formula approximates the integral,

      [ ∫_{-1}^1 f(x) dx ].

    The corresponding orthogonal polynomials are called Legendre polynomials.
*)

(** _Editor's note:  Thus ends Stewart's presentation, except for paragraph 22 (Gauss-Laguerre
     quadrature), paragraph 23 (Gauss-Hermite quadrature), and paragraph 24 (there are many
     other such Gauss formulas suitable for special purposes). In the remainder of this file, 
     your humble editor permits himself to write in Roman font, not Italic. -- Andrew Appel_ *)

Module Legendre.
 Section R.
 Context {R : realType}.
 Definition lo : R := -1.
 Definition hi : R := 1.
 Lemma lo_lt_hi: (lo < hi)%R.    Proof. rewrite /lo /hi; lra. Qed.
 Definition w (x: R) : R := 1.
 Lemma w_positive: forall x, is_true (lo <= x <= hi) -> is_true (0 < w x).
 Proof. intros. rewrite /w. lra. Qed.
 Lemma wcontinuous:     {in `[lo, hi], continuous w}%classic.
 Proof. rewrite /w. intros ? ?. apply (@cst_continuous R R 1 x). Qed.
 
 Hint Resolve wcontinuous: continuous.

 Definition legendre (n: nat) : {poly R} :=  ortho_p lo hi w n.

 (** Presto! the Legendre polynomials have been defined.  But we want to put
  them into a much more usable form.  The remainder of this Module Legendre
  will instantiate the theory of orthogonal polynomials for this instance,
  then prove specific useful things (in this theory) about the Legendre polynomials of 
  degree up to 4. *)

 (** First, instantiate the notion of integral from lo to hi, from the general theory into the specific: *)

 Definition intgal := @intgal R lo hi w.
 Notation "∫" := intgal.

 Lemma intgal_eq: forall f,
       ∫ f = \int[lebesgue_measure]_(x in `[lo,hi]%classic) (f x).
(* begin details: Proof ... Qed. *)
 Proof. intros. rewrite /intgal /quadrature.intgal. f_equal. extensionality x. rewrite /w mulr1 //. Qed.
(* end details *)


(* begin details: A whole bunch of useful rewriting lemmas, to be used automatically in the rewrite tactic *)

Lemma intgal_linear1 : forall (α : R) (f : R -> R),
  {in `[lo, hi], continuous f}%classic ->
   ∫ (α \*: f) =  α * ∫ f.
Proof.
intros. rewrite /intgal intgal_linear1 -/intgal //. apply lo_lt_hi. apply wcontinuous.
Qed.

Lemma intgal_linear1' : forall (α : R) (f : {poly R}),   ∫ (horner (polyC α * f)) =  α * ∫ (horner f).
Proof.
intros.
rewrite -intgal_linear1; auto with continuous.
f_equal. extensionality x. rewrite hornerE //.
Qed.

Lemma intgal_linear1'' : forall (α : R) (f : {poly R}), ∫ (horner ((- polyC α) * f)) =  (-α) * ∫ (horner f).
Proof.
intros.
rewrite -intgal_linear1; auto with continuous.
f_equal. extensionality x. rewrite ?hornerE //.
Qed.

Lemma intgal_linearN : forall (f : R -> R), 
  {in `[lo, hi], continuous f}%classic ->
  ∫ (opp_fun f) =  - ∫ f.
Proof.
intros.
transitivity ( ∫ ((fun=> -1)  \* f)).
f_equal; extensionality x; simpl; lra.
rewrite intgal_linear1; auto.
lra.
Qed.

Lemma intgal_linearN' : forall (f : {poly R}), ∫ (horner (-f)) =  - ∫ (horner f).
Proof.
intros.
rewrite -intgal_linearN; auto with continuous.
f_equal. extensionality x. rewrite hornerE //.
Qed.

Lemma intgal_linear2: forall  f g : R -> R, 
  {in `[lo, hi], continuous f}%classic ->
  {in `[lo, hi], continuous g}%classic ->
   ∫ (f \+ g) =  ∫ f +  ∫ g.
Proof.
intros. rewrite /intgal intgal_linear2 -/intgal; auto with continuous. 
Qed.

Lemma intgal_linear2': forall  f g : {poly R},  ∫ (horner (f + g)) =  ∫ (horner f) +  ∫ (horner g).
Proof.
intros.
rewrite -intgal_linear2; auto with continuous.
f_equal. extensionality x. rewrite hornerE //.
Qed.

Definition intgal_linear := (intgal_linear1'', intgal_linear1', intgal_linear1, intgal_linearN, intgal_linearN', intgal_linear2', intgal_linear2).
(* end details *)

(** ** Packaging the Legendre polynials *)

(** We want to build packages, for each n up to degree 4, of:
  - LR_poly:  the conventional simplified form of the normalized Legendre polynomial
    (in contrast to ortho_p which produces a very large expression); 
  - LR_poly_eq: a proof that the legendre polynomial constructed by the three-term recurrence
     really is equal to LR_poly;
  - LR_roots: an instance of the roots_of_ortho_p package, which itself is an n.-tuple of roots
     along with proofs that they are strictly sorted and really evaluate to zero. 
*)

Record legendre_roots (n: nat) := {
   LR_poly: {poly R};
   LR_poly_eq: legendre n = LR_poly;
   LR_roots: roots_of_ortho_p lo hi w n
}.
Arguments LR_poly [n].
Arguments LR_poly_eq [n].
Arguments LR_roots [n].
Arguments Build_legendre_roots [n].

(** Similarly, we will build packages, for each n up to degree 4, of the gauss weights
    for the nth Legendre polynomial. *)
Record gauss_weights (n: nat) := {
   GW_legendre: legendre_roots n;
   GW_vals: n.-tuple R;
   GW_good: forall i, gauss_weight _ _ _ _ (LR_roots GW_legendre) i = tnth GW_vals i
}.
Arguments GW_legendre [n].
Arguments GW_vals [n].
Arguments GW_good [n].
Arguments Build_gauss_weights [n].

(** The following is a concrete implementation of the formula G_n(f) in Stewart's paragraph 15. *)

 Definition compute_G [n] (GW: gauss_weights n) (f: R -> R) :=
  \sum_i (tnth (GW_vals GW) i) * f (tnth (ROOTS_vals lo hi w n (LR_roots (GW_legendre GW))) i).

Lemma compute_G_eq: forall n (GW: gauss_weights n) f, 
  compute_G GW f = G lo hi w n (LR_roots (GW_legendre GW)) f.
(* begin details:  Proof.  ... Qed. *)
Proof.
intros.
rewrite /compute_G /G.
f_equal.
extensionality i.
f_equal; f_equal; symmetry; apply GW_good.
Qed.
(* end details *)

(** Now we instantiate the general quadrature_error theorem for the instance of
   Legendre polynomials *)

 Lemma legendre_quadrature_error: forall [n: nat] (GW: gauss_weights n) (f: R -> R),
      exists ξ:R, lo <= ξ <= hi /\
       ∫ f - compute_G GW f =  derive1n (2*n+2) f ξ / 
       (factorial(2*n+2))%:R * ∫ (fun x => (horner (legendre n.+1) x)^2).
Proof.
intros.
rewrite compute_G_eq /intgal.
apply quadrature_error; auto; auto with continuous. apply lo_lt_hi.
Qed.

(* begin details:  A bunch of useful rewriting rules *)

Definition r_integral:
 forall P : {poly R}, \int[lebesgue_measure]_(x in `[lo, hi]) P.[x] = (integ P).[hi] - (integ P).[lo]
 := Rintegral_poly _ _ lo_lt_hi.

Lemma intgal_X: ∫ (horner 'X) = 0.
Proof.
rewrite polyX' intgal_eq  r_integral /lo /hi /integ /= ?hornerE ?horner_poly.
repeat expand_bigop.
ring.
Qed.

Lemma intgal_0: ∫ (horner 0%:P) = 0.
Proof.
rewrite polyC0 intgal_eq ?r_integral /lo /hi /integ /= ?hornerE ?horner_poly.
rewrite size_poly0.
repeat expand_bigop.
ring.
Qed.

Lemma intgal_1: ∫ (horner 1%:P) = 2.
Proof.
rewrite polyC1 intgal_eq ?r_integral /lo /hi /integ /= ?hornerE ?horner_poly size_polyC oner_neq0 /= polyseq1.
repeat expand_bigop.
field; auto.
Qed.

Lemma intgal_C: forall c,  ∫ (horner c%:P) = 2*c.
Proof.
intros. rewrite -(mulr1 c%:P) ?intgal_linear intgal_1 mulrC //.
Qed.

Lemma intgal_X2: ∫ (horner ('X * 'X)) = 2/3.
Proof.
rewrite polyX2' intgal_eq ?r_integral /lo /hi /integ /= ?hornerE ?horner_poly.
repeat expand_bigop.
ring.
Qed.

Lemma intgal_X3: ∫ (horner ('X * ('X * 'X))) = 0.
Proof.
rewrite polyX3' intgal_eq ?r_integral /lo /hi /integ /= ?hornerE ?horner_poly.
repeat expand_bigop.
ring.
Qed.

Lemma intgal_X4: ∫ (horner ('X * ('X * ('X * 'X)))) = 2/5.
Proof.
rewrite polyX4' intgal_eq ?r_integral /lo /hi /integ /= ?hornerE ?horner_poly.
repeat expand_bigop.
ring.
Qed.

Lemma intgal_X5:  ∫ (horner ('X * ('X * ('X * ('X * 'X))))) = 0.
Proof.
rewrite polyX5' intgal_eq ?r_integral /lo /hi /integ /= ?hornerE ?horner_poly.
repeat expand_bigop.
ring.
Qed.

Lemma intgal_X6:  ∫ (horner ('X * ('X * ('X * ('X * ('X * 'X)))))) = 2/7.
Proof.
rewrite polyX6' intgal_eq ?r_integral /lo /hi /integ /= ?hornerE ?horner_poly.
repeat expand_bigop.
ring.
Qed.

Lemma intgal_X7:  ∫ (horner ('X * ('X * ('X * ('X * ('X * ('X * 'X))))))) = 0.
Proof.
rewrite polyX7' intgal_eq ?r_integral /lo /hi /integ /= ?hornerE ?horner_poly.
repeat expand_bigop.
ring.
Qed.

Lemma intgal_X8:  ∫ (horner ('X * ('X * ('X * ('X * ('X * ('X * ('X * 'X)))))))) = 2/9.
Proof.
rewrite polyX8' intgal_eq ?r_integral /lo /hi /integ /= ?hornerE ?horner_poly.
repeat expand_bigop.
ring.
Qed.

Definition r_intgal := (intgal_linear, intgal_0, intgal_1, intgal_C, intgal_X, intgal_X2, 
                      intgal_X3, intgal_X4, intgal_X5, intgal_X6, intgal_X7, intgal_X8).

Lemma pull_left1: forall u: {poly R}, 'X * u = u * 'X.
Proof. intros. ring. Qed.

Lemma pull_left2: forall u v: {poly R}, 'X * (u * v) = u * ('X * v).
Proof. intros. ring. Qed.

Definition pull_left (u: {poly R}) := (pull_left1 u, pull_left2 u).


Lemma pull_left1': forall u: R, 'X * (polyC u) = (polyC u) * 'X.
Proof. intros. ring. Qed.

Lemma pull_left2': forall (u: R) (v: {poly R}), 'X * (polyC u * v) = polyC u * ('X * v).
Proof. intros. ring. Qed.

Lemma scale_polyC': forall x y: R, scale_poly x (polyC y) = polyC (x*y).
Proof.
intros.
rewrite scale_polyE mul_polyC' //.
Qed.

Lemma mulrA'X: forall a b c: {poly R}, a * b * c = a * (b * c).
Proof.
symmetry. apply mulrA.
Qed.

Definition norm_poly := (mulrA'X, pull_left1', pull_left2', scale_1poly, scale_0poly, scale_polyC', r_ring, r_intgal).

Definition mulrD {R: pzRingType} := (@mulrDr R, @mulrDl R, @mulrN R, @mulNr R, @opprK R).

Lemma hornerD'': forall (a b: {poly R}), @horner R (a-b) = horner a \- horner b.
Proof. intros. extensionality x. rewrite hornerD. rewrite hornerN. reflexivity.
Qed.

Lemma eq_opI: forall {s} (A B: Equality.sort s), A=B -> is_true (eq_op A B).
Proof.
intros.
subst.
apply eq_refl.
Qed.

Lemma sub_mul2: forall (x :R), -x-x = -(2*x).
Proof. intros. lra. Qed.

Lemma opp_sub: forall {s: zmodType} (x y:s), -x-y = -(x+y).
Proof. intros.
pose proof (opprB x (-y)).
rewrite opprK in H. rewrite H. apply addrC.
Qed.

Ltac do_one_integral u := 
let i := fresh "i" in let g := fresh "g" in 
set i := ∫ _;  pattern i; match goal with |- ?G _ => set g := G end; subst i;
rewrite ?mulrD -?mulrA ?(pull_left u) ?r_intgal ?r_ring; subst g; cbv beta; rewrite ?r_ring ?scale_0poly ?r_ring.

(* end details *)

(** *** The degree-0 Legendre polynomial *)

(** First, prove that the 0-th Legendre polynomial, as constructed by the [ortho_p]
    recurrence, is the constant function 1.  This is rather trivial, but when we get to n=3
    and n=4 it won't be so easy. *)
Lemma Legendre_poly_0: legendre 0 = 1%:P.
Proof.
rewrite /legendre /ortho_p /= ?scale_polyE ?r_intgal ?r_ring //.
Qed.

Lemma Legendre_poly_0': horner (legendre 0) = fun x: R => 1.
Proof.
rewrite Legendre_poly_0 ?r_horner //.
Qed.

(** Second, package up the [legendre_roots] structure for degree 0 *)
Definition legendre_roots_0 : legendre_roots 0.
  apply (Build_legendre_roots _ Legendre_poly_0).
  apply (Build_roots_of_ortho_p lo hi _ 0 (@Tuple 0 _ nil isT)).
- constructor.
- reflexivity.
- reflexivity.
Defined.

(** *** The degree-1 Legendre polynomial *)

Lemma Legendre_poly_1: legendre 1 = 'X.
Proof.
rewrite /legendre /ortho_p /= hornerX_i -?hornerM' ?mulr1 ?mul1r ?mulr0 ?mul0r -/intgal ?r_intgal ?scale_polyE.
ring.
Qed.

Lemma Legendre_poly_1': horner (legendre 1) =  fun x:R => x.
Proof.
rewrite Legendre_poly_1 ?r_horner //.
Qed.

Definition legendre_roots_1: legendre_roots 1.
  apply (Build_legendre_roots _ Legendre_poly_1).
 apply (Build_roots_of_ortho_p lo hi _ _ (@Tuple 1 _ [:: 0] isT)).
-
simpl; red; rewrite ?Bool.andb_true_iff; repeat split;
rewrite /root -/(legendre _).
rewrite Legendre_poly_1.
rewrite hornerE.
apply eq_refl.
-
reflexivity.
-
simpl; red; rewrite /lo /hi ?Bool.andb_true_iff; repeat split;  lra.
Defined.


(** *** The degree-2 Legendre polynomial *)
Lemma Legendre_poly_2:  legendre 2 =   'X*'X - (1/3)%:P.
Proof.
rewrite /legendre /ortho_p /= -?hornerX' -?hornerM' ?r_ring.
rewrite -/intgal ?r_intgal ?r_ring ?scale_0poly ?scale_1poly ?r_ring.
rewrite ?r_intgal ?r_ring scale_0poly ?r_ring scale_polyE mulr1.
f_equal.
f_equal.
f_equal. 
field; auto.
Qed.

Lemma Legendre_poly_2': horner (legendre 2) =   fun x :R => x*x - 1/3.
Proof.
rewrite Legendre_poly_2 ?r_horner //.
Qed.

(** Now we start to need square roots.  It could be worse: above degree 4, the roots
  don't even have closed-form expressions with square roots.  Fortunately, we don't 
  need to go above degree 4. *)
Notation sqrt := (@Num.sqrt R).

Lemma sqrt_exists: forall (x: R), 0 < x -> 
 in_mem (sqrt x) (mem unit).
Proof.
intros.
rewrite -sqrtr_gt0 in H.
apply unitf_gt0; auto.
Qed.

Lemma sqr_sqrt: forall x:R, 0 <= x -> (sqrt x * sqrt x) = x.
Proof.
intros.
apply sqr_sqrtr; auto.
Qed.

(** The roots of the degree-2 Legendre polynomial are  -1/sqrt(3) and +1/sqrt(3).  *)
Definition legendre_roots_2: legendre_roots 2.
  apply (Build_legendre_roots _ Legendre_poly_2).
 apply (Build_roots_of_ortho_p lo hi _ _ (@Tuple 2 _ [:: -1/(sqrt 3); 1/(sqrt 3)]  isT)).
-
simpl; red;
rewrite /root -/(legendre _);
 rewrite Legendre_poly_2 ?hornerE /=.
 rewrite ?Bool.andb_true_iff; repeat split; apply eq_opI.
 + rewrite ?mulN1r ?mulrNN ?mulr1 -invrM; [ | apply sqrt_exists; lra .. ].
    rewrite sqr_sqrt; lra.
 + rewrite mulr1 -invrM; [ | apply sqrt_exists; lra .. ].
    rewrite sqr_sqrt; lra.
-
  simpl; red; rewrite ?Bool.andb_true_iff; repeat split.
  assert (0 <  1 / sqrt 3)
  by (apply divr_gt0; rewrite ?sqrtr_gt0; lra).
  lra.
-  
  assert (0 <  1 / sqrt 3) by (apply divr_gt0; rewrite ?sqrtr_gt0; lra).
  assert (sqrt 3 > 1) by (rewrite -{1}sqrtr1; rewrite ltr_sqrt; lra).
  assert (1 / sqrt 3 < 1) by (rewrite mul1r invf_lt1; lra).
  simpl; red; rewrite ?Bool.andb_true_iff; repeat split; rewrite /lo /hi; lra.
Defined.

Lemma mul_polyC_polyC: forall {R} (x y: NzSemiRing.sort R), 
  polyC x * polyC y = polyC (x*y).
Proof.
intros.
rewrite -(mulr1 (polyC y)).
rewrite -(mulr1 (polyC (mul x y))).
rewrite ?mul_polyC.
rewrite scalerA //.
Qed.

Lemma add_polyC_polyC: forall {R} (x y: NzSemiRing.sort R), 
  polyC x + polyC y = polyC (x+y).
Proof.
intros.
rewrite -polyP.
intro i.
rewrite coefC.
change (add (polyC x) (polyC y)) with (add_poly (polyC x) (polyC y)).
rewrite coef_add_poly ?coefC.
destruct (eq_op _ _); auto.
rewrite addr0 //.
Qed.

(** *** The degree-3 Legendre polynomial *)
Lemma Legendre_poly_3: legendre 3 =  'X*'X*'X - (3/5)%:P*'X.
Proof.
rewrite /legendre /ortho_p /= -?hornerX' -?hornerM' ?r_ring.
rewrite -/intgal ?norm_poly ?mulrD ?norm_poly.
rewrite scale_polyE.
rewrite -addrA.
f_equal.
rewrite opp_sub.
f_equal.
rewrite -?mulrDl.
f_equal.
rewrite add_polyC_polyC.
f_equal.
field; auto.
Qed.

Lemma Legendre_poly_3': horner (legendre 3) =  fun x :R => x*x*x - (3/5)*x.
Proof.
rewrite Legendre_poly_3 ?r_horner //.
Qed.

(** The roots of the degree-2 Legendre polynomial are  -sqrt(3/5), 0, and +sqrt(3/5).  *)
Definition legendre_roots_3: legendre_roots 3.
  apply (Build_legendre_roots _ Legendre_poly_3).
 apply (Build_roots_of_ortho_p lo hi _ _ (@Tuple 3 _ [:: -(sqrt (3/5)); 0; (sqrt (3/5))]  isT)).
-
simpl; red;
rewrite /root -/(legendre _);
 rewrite Legendre_poly_3 ?hornerE.
 rewrite ?Bool.andb_true_iff; repeat split; apply eq_opI;
  rewrite /tnth /= ?mulrNN ?sqr_sqrt; lra.
-
  assert (0 <  sqrt (3/5)) by (rewrite sqrtr_gt0; lra).
  simpl; red; rewrite ?Bool.andb_true_iff; repeat split; lra.
-
  assert (0 < sqrt (3/5)) by  (rewrite ?sqrtr_gt0; lra).
  assert (sqrt(3/5) < 1) by (rewrite -{3}sqrtr1 ltr_sqrt; lra).
  simpl; red; rewrite ?Bool.andb_true_iff; repeat split; rewrite /lo /hi; lra.
Defined.

(** *** The degree-4 Legendre polynomial *)

Lemma Legendre_poly_4:  legendre 4 =  'X*'X*'X*'X - (30/35)%:P*('X*'X) + (3/35)%:P.
(* These proofs are getting longer and longer! *)
Proof.
rewrite /legendre /ortho_p /= -?hornerX' -?hornerM' ?r_ring.
match goal with |- _ = ?B => set RHS := B end.
rewrite -/intgal ?r_intgal ?r_ring ?scale_0poly ?scale_1poly ?r_ring.
rewrite ?r_intgal ?r_ring ?scale_0poly ?r_ring scale_polyE ?r_ring.
set u := ( _ / _ / _)%:P.
rewrite (invf_div 2 3).
set v := 3/2.
rewrite ?scale_polyE.
repeat do_one_integral u.
subst v.
set a := 2/5 - _.
set b := inv _ * _.
set c := inv _ * _.
rewrite ?norm_poly.
rewrite ?mulrD ?norm_poly.
subst RHS.
rewrite -?addrA.
f_equal.
ring.
rewrite mul_polyC_polyC.
set u1 := polyC _.
set u2 := polyC _.
set u3 := polyC _.
set u4 := polyC _.
set u5 := polyC _.
rewrite -opp_sub opprK.
rewrite ?addrA.
f_equal.
rewrite ?opp_sub.
f_equal.
rewrite -?mulrDl.
f_equal.
subst u1 u2 u3 u5.
rewrite ?add_polyC_polyC.
f_equal.
field; auto.
subst u4; f_equal; field; auto.
Qed.

Lemma Legendre_poly_4': horner (legendre 4) =  fun x :R => x*x*x*x - (30/35)*(x*x) + (3/35).
Proof.
rewrite Legendre_poly_4 ?r_horner //.
Qed.

Definition legendre_roots_val := 
  @Tuple 4 _ 
    [:: -(sqrt ((3 + 2 * sqrt(6/5))/7)); -(sqrt ((3 - 2 * sqrt(6/5))/7)); 
         (sqrt ((3 - 2 * sqrt(6/5))/7)); (sqrt ((3 + 2 * sqrt(6/5))/7)) ] isT.

Lemma legendre_roots_4a: 
   is_true (all (root (ortho_p lo hi w 4)) (tval legendre_roots_val)).
(* begin details: Proof. ... Qed. *)
Proof.
simpl.
assert (H3: is_true (0 <= (3 - 2 * sqrt (6 / 5)) / 7)). {
  assert (3/(2) >= sqrt (6/5))%R; [ | nra].
  assert (sqrt (9/4) = 3/2).
  transitivity (sqrt ((3/2) * (3/2))). f_equal; lra.
  rewrite sqrtrM ?sqr_sqrt; lra.
  rewrite -H ler_sqrt; lra.
}
assert (H4: 0 < sqrt (6/5)) by (rewrite sqrtr_gt0; lra).
simpl; red;
rewrite /root -/(legendre _);
 rewrite Legendre_poly_4'.
 rewrite ?Bool.andb_true_iff; repeat split; apply eq_opI.
+
rewrite ?mulrNN.
rewrite -mulrA ?mulrNN sqr_sqrt; try lra.
pose proof (sqr_sqrt (6/5) ltac:(lra)).
set a := sqrt (_/_) in H,H3,H4|-*. simpl in a.
set b := 2*a.
assert (b*b = 24/5) 
  by (rewrite /b {1}(mulrC 2) mulrA (mulrC (_ * _ * _)); lra).
lra.
+
rewrite ?mulrNN.
rewrite -mulrA ?mulrNN.
rewrite sqr_sqrt; try lra.
pose proof (sqr_sqrt (6/5) ltac:(lra)).
set a := sqrt (_/_) in H4,H3,H|-*. simpl in a.
set b := 2*a.
assert (b*b = 24/5) 
  by (rewrite /b {1}(mulrC 2) mulrA (mulrC (_ * _ * _)); lra).
lra.
+
rewrite ?mulrNN.
rewrite -mulrA ?mulrNN.
rewrite sqr_sqrt; try lra.
pose proof (sqr_sqrt (6/5) ltac:(lra)).
set a := sqrt (_/_) in H,H3,H4|-*. simpl in a.
set b := 2*a.
assert (b*b = 24/5) 
  by (rewrite /b {1}(mulrC 2) mulrA (mulrC (_ * _ * _)); lra).
lra.
+
rewrite ?mulrNN.
rewrite -mulrA ?mulrNN.
rewrite sqr_sqrt; try lra.
pose proof (sqr_sqrt (6/5) ltac:(lra)).
set a := sqrt (_/_) in H3,H4,H|-*. simpl in a.
set b := 2*a.
assert (b*b = 24/5) 
  by (rewrite /b {1}(mulrC 2) mulrA (mulrC (_ * _ * _)); lra).
lra.
Qed.
(* end details *)

Lemma legendre_roots_4b:
  is_true (sorted <%R (tval legendre_roots_val)).
(* begin details: Proof. ... Qed. *)
Proof.
assert (H4: 0 < sqrt (6/5)) by (rewrite sqrtr_gt0; lra).
  simpl; red; rewrite ?Bool.andb_true_iff; repeat split.
+ rewrite lterNl opprK ltr_sqrt; lra.
+
match goal with |-  (- ?A < _) = true => assert (0 < A); [ | lra] end.
rewrite sqrtr_gt0.
assert (sqrt (6/5) <= 6/5); [ | lra].
assert (6/5 = sqrt ((6/5)*(6/5))). 
rewrite sqrtrM ?sqr_sqrt ; lra.
rewrite H.
rewrite ler_sqrt.
rewrite -H. lra. lra.
+
rewrite ltr_sqrt; lra.
Qed.
(* end details *)

Lemma legendre_roots_4c:
 is_true   (all (fun x : Order.Preorder.sort (reals_Real__to__Order_Preorder R) => lo <= x <= hi)
     (tval legendre_roots_val)).
(* begin details: Proof. ... Qed. *)
Proof.
assert (1 < sqrt (6/5)) by (rewrite -{1}sqrtr1 ltr_sqrt;  lra).
assert (sqrt(6/5)<6/5) by (rewrite -{2}(sqr_sqrt (6/5)); nra).
assert (0 < sqrt((3%R + (2 * Num.ExtraDef.sqrtr (6 / 5))%R)%E / 7))
   by (rewrite sqrtr_gt0; lra).
assert (sqrt((3%R + (2 * Num.ExtraDef.sqrtr (6 / 5))%R)%E / 7) < 1) 
  by ( rewrite -{6}sqrtr1 ltr_sqrt; lra).
assert (0 < sqrt((3 - (2 * Num.ExtraDef.sqrtr (6 / 5))) / 7))
   by (rewrite sqrtr_gt0; lra).
assert (sqrt((3 - (2 * Num.ExtraDef.sqrtr (6 / 5))) / 7) < 1) 
  by ( rewrite -{6}sqrtr1 ltr_sqrt; lra).
  simpl; red; rewrite ?Bool.andb_true_iff; repeat split; rewrite /lo /hi; lra.
Qed.
(* end details *)

Definition legendre_roots_4: legendre_roots 4.
  apply (Build_legendre_roots _ Legendre_poly_4).
 apply (Build_roots_of_ortho_p lo hi _ _  legendre_roots_val
   legendre_roots_4a legendre_roots_4b legendre_roots_4c).
Defined. 

(** ** Building the Gauss weights of Legendre polynomials *)

(** *** Gauss weights of degree-0 Legendre polynomials *)

Definition gauss_weights_0 : gauss_weights 0.
 apply (Build_gauss_weights legendre_roots_0 [::]).
 intros.
 ord_enum_cases i.
  (* no cases *)
 Defined.


(** *** Gauss weights of degree-1 Legendre polynomials *)
(**  The Gauss weights of degree 1 is just the singleton 2. *)
Lemma gauss_weight_1_0: gauss_weight _ _ _ _ (LR_roots legendre_roots_1) (@Ordinal 1 0 isT) = 2.
Proof.
rewrite /gauss_weight /legendre_roots_1 /LR_roots /L /zeros_of_ortho_p /ROOTS_vals.
rewrite lagrangeE;  [ | Lia.lia | apply extend_roots_injective; apply lo_lt_hi].
 cbv zeta; expand_bigop.
  rewrite /extend_roots /= ?r_horner invr1 ?r_lift.
  rewrite (_: (fun=>1) = horner (polyC 1)).
  2: extensionality x; rewrite hornerE //.
  rewrite -/intgal intgal_C mulr1 //.
Qed.

Definition gauss_weights_1 : gauss_weights 1.
 apply (Build_gauss_weights legendre_roots_1 [:: 2 ]).
 intros. 
 ord_enum_cases i.
 - (* case 0 *) apply gauss_weight_1_0.
Defined.


(** *** Gauss weights of degree-2 Legendre polynomials *)
(**  The Gauss weights of degree 2 are the sequence 1,1. *)
Lemma gauss_weight_2_0: gauss_weight _ _ _ _ (LR_roots legendre_roots_2) (@Ordinal 2 0 isT) = 1.
Proof.
rewrite /gauss_weight /legendre_roots_2 /LR_roots /L /zeros_of_ortho_p /ROOTS_vals.
rewrite lagrangeE;  [ | Lia.lia | apply extend_roots_injective; apply lo_lt_hi].
cbv zeta; expand_bigop.
rewrite /extend_roots /= ?r_horner ?r_ring ?r_lift.
set s3 := Num.sqrt 3. simpl in s3.
rewrite -(div1r s3) mulN1r -/intgal.
transitivity ( ∫ (horner ('X * -(s3/2)%:P + (1/2)%:P))).
-
f_equal.
extensionality x.
simpl.
rewrite ?hornerE.
field.
assert (0 < s3); rewrite ?sqrtr_gt0; lra.
-
transitivity ( ∫ (horner (-(s3/2))%:P \* (horner 'X) \+ horner (1/2)%:P)).
f_equal; extensionality x; rewrite ?hornerE /= ?hornerE;  lra.
rewrite -hornerM' ?r_intgal ?r_ring; auto with continuous.
lra.
Qed.

Lemma gauss_weight_2_1: gauss_weight _ _ _ _ (LR_roots legendre_roots_2) (@Ordinal 2 1 isT) = 1.
Proof.
rewrite /gauss_weight /legendre_roots_2 /LR_roots /L /zeros_of_ortho_p /ROOTS_vals.
rewrite lagrangeE;  [ | Lia.lia | apply extend_roots_injective; apply lo_lt_hi ].
cbv zeta.
expand_bigop.
  rewrite /extend_roots /= ?r_horner ?r_lift
        -/intgal ?r_ring -hornerX' -?hornerC' -?hornerD' -?hornerD''
        -hornerM' ?r_intgal ?r_ring.
field.
assert (0 < sqrt 3);  rewrite ?sqrtr_gt0; lra.
Qed.

Definition gauss_weights_2 : gauss_weights 2.
 apply (Build_gauss_weights legendre_roots_2 [:: 1; 1]).
Proof.
intros.
 ord_enum_cases i.
 - (* case 0 *) apply gauss_weight_2_0.
 - (* case 1 *) apply gauss_weight_2_1.
Defined.

(** *** Gauss weights of degree-3 Legendre polynomials *)
(**  The Gauss weights of degree 3 are 5/9, 8/9, 5/9. *)

Lemma gauss_weight_3_0: gauss_weight _ _ _ _ (LR_roots legendre_roots_3) (@Ordinal 3 0 isT) = 5/9.
Proof.
rewrite /gauss_weight /legendre_roots_3 /LR_roots /L /zeros_of_ortho_p /ROOTS_vals.
rewrite lagrangeE;  [ | Lia.lia | apply extend_roots_injective; apply lo_lt_hi].
cbv zeta; expand_bigop.
  rewrite /extend_roots /= ?r_horner ?r_lift
  -/intgal ?r_ring -hornerX' -?hornerC' -?hornerD' -?hornerD''.
set s3 := Num.sqrt (3/5). simpl in s3.
rewrite -?hornerM'.
rewrite (_: - s3 - s3 = -(s3 * 2) :> R); [ | lra].
rewrite mulrNN (mulrA s3) {1 2}/s3.
rewrite sqr_sqrt ; [ | lra].
rewrite (mulrC _ 2) mulrA.
do_one_integral (s3%:P).
field; auto.
Qed.

Lemma gauss_weight_3_1: gauss_weight _ _ _ _ (LR_roots legendre_roots_3) (@Ordinal 3 1 isT) = 8/9.
Proof.
rewrite /gauss_weight /legendre_roots_3 /LR_roots /L /zeros_of_ortho_p /ROOTS_vals.
rewrite lagrangeE;  [ | Lia.lia | apply extend_roots_injective; apply lo_lt_hi ].
cbv zeta; expand_bigop.
  rewrite /extend_roots /= ?r_horner ?r_lift.
rewrite -/intgal ?r_ring -hornerX' -?hornerC' -?hornerD' -?hornerD''.
set s3 := Num.sqrt (3/5). simpl in s3.
rewrite -?hornerM'.
rewrite opprK mulrN.
rewrite sqr_sqrt; [ | lra].
do_one_integral (- s3)%:P.
do_one_integral s3%:P.
rewrite mulNr.
rewrite (mulrC 2 s3).
rewrite (mulrA s3).
rewrite sqr_sqrt ; [ | lra].
field; auto.
Qed.

Lemma gauss_weight_3_2: gauss_weight _ _ _ _ (LR_roots legendre_roots_3) (@Ordinal 3 2 isT) = 5/9.
Proof.
rewrite /gauss_weight /legendre_roots_3 /LR_roots /L /zeros_of_ortho_p /ROOTS_vals.
rewrite lagrangeE;  [ | Lia.lia | apply extend_roots_injective; apply lo_lt_hi ].
cbv zeta; expand_bigop.
  rewrite /extend_roots /= ?r_horner ?r_lift.
rewrite -/intgal ?r_ring -hornerX' -?hornerC' -?hornerD' -?hornerD''.
set s3 := Num.sqrt (3/5). simpl in s3.
rewrite -?hornerM'.
set u := _ - _. replace u with ((s3 * 2))%R by (subst u; lra). clear u.
rewrite -(mulrA s3).
rewrite (mulrC 2 s3) ?mulrA.
rewrite sqr_sqrt ; [ | lra].
do_one_integral (- s3)%:P.
field; auto.
Qed.

Definition gauss_weights_3 : gauss_weights 3.
 apply (Build_gauss_weights legendre_roots_3 [:: 5/9; 8/9; 5/9]).
Proof.
intros.
ord_enum_cases i.
apply gauss_weight_3_0.
apply gauss_weight_3_1.
apply gauss_weight_3_2.
Defined.

(** *** Gauss weights of degree-4 Legendre polynomials *)
(**  The Gauss weights of degree 3 are 1/2-sqrt(5/6)/6, 1/2+sqrt(5/6)/6, 1/2+sqrt(5/6)/6, 1/2-sqrt(5/6)/6. *)

Lemma add_mul2: forall (x :R), x+x = 2*x.
Proof. intros. lra. Qed.

Lemma add_mul3: forall (x :R), x+(x+x) = 3*x.
Proof. intros. lra. Qed.

Lemma gauss_weight_4_0: gauss_weight _ _ _ _ (LR_roots legendre_roots_4) (@Ordinal 4 0 isT) = 
       1/2 - Num.sqrt(5/6)/6.
(* begin details: Proof.  ... very long and tedious ... Qed. *)
Proof.
set RHS := _ - _.
rewrite /gauss_weight /legendre_roots_4 /LR_roots /L /zeros_of_ortho_p /ROOTS_vals.
rewrite lagrangeE;  [ | Lia.lia | apply extend_roots_injective; apply lo_lt_hi].
cbv zeta; expand_bigop.
  rewrite /extend_roots /= ?r_horner ?r_lift.
rewrite -/intgal ?r_ring -hornerX' -?hornerC' -?hornerD' -?hornerD'' ?r_ring.
set s3 := Num.sqrt (6/5). simpl in s3.
rewrite opprK.
set a := inv _.
set b := Num.sqrt _.
set c := Num.sqrt _. simpl in a,b,c.
assert (is_true (1 < s3)) by (rewrite -{1}sqrtr1 ltr_sqrt;  lra).
assert (s3<6/5). rewrite -(sqr_sqrt (6/5)) -/s3; try lra. nra.
assert (is_true (0 <= (3 - 2 * s3) / 7)) by nra.
set u := - b - b; replace u with (-2*b) by (subst u; lra); clear u.
rewrite -?hornerM'.
rewrite r_intgal.
rewrite ?(@mulrD {poly _}) -?mulrA.
rewrite ?(pull_left (-c%:P)) ?r_intgal ?r_ring.
rewrite ?(pull_left (b%:P)) ?r_intgal ?r_ring.
rewrite ?(pull_left (c%:P)) ?r_intgal ?r_ring.
transitivity (a * ((- c * (2 / 3))%R + (- b * (2 / 3))%R + ((b * (2 / 3))%R + (- (b * b) * (2 * - c))%R))%E); [ ring | ].
rewrite sqr_sqrt; try lra. 
rewrite addrA. 
rewrite (mulNr b).
rewrite ?mulrDr ?mulrDl.
rewrite ?mulNr ?mulrN.
set u := a * (b * _).
rewrite add_mul2.
rewrite ?mul1r.
rewrite add_mul3.
clearbody u. simpl in u.
rewrite add_mul2.
rewrite add_mul2 ?mulrN opprK.
set d := - (_ * _).
simpl  in d.
rewrite -(addrA d).
rewrite (addrC (opp u)).
replace (d + _) with d by lra.
clear u.
subst d.
rewrite !mulrA.
rewrite (mulrC (_ * _) c).
rewrite !mulrA.
rewrite (mulrC c a).
rewrite -(mulrA _ 2 (inv 3)).
rewrite -(mulrN (a*c)).
rewrite -(mulrA (a*c)).
rewrite -mulrDr.
set (d := _ * 2).
subst a c.
set a := Num.sqrt _.
set c := Num.sqrt _.
simpl in *.
rewrite add_mul2 ?mulrN ?mulNr.
rewrite mulrA.
set e := _ * (- a - c).
replace e with (a*a - c*c) by (subst e; nra).
clear e.
rewrite !sqr_sqrt; try (subst a c; lra).
clear c.
clear b.
set u := _ / 7 - _ / 7.
replace u with ((4/7)*s3) by (subst u; nra). clear u.
rewrite ?mulrA.
rewrite invrN mulNr.
rewrite invrM; try (rewrite unitfE; lra).
2: rewrite unitfE; assert (0 < a) by (rewrite sqrtr_gt0; lra);  lra.
rewrite (mulrC _ a).
rewrite mulrA.
rewrite mulfV.
2: assert (0 < a) by (rewrite sqrtr_gt0; lra);  lra.
clear a.
subst d.
rewrite -(mulNr (2*s3) (inv 7)).
rewrite -mulrDl.
rewrite r_ring.
rewrite addrC.
rewrite -(mulrA _ s3).
rewrite (mulrC _ (s3 * _)).
rewrite (mulrA (s3 * 2)).
rewrite invrM; [  |  rewrite unitfE; lra ..].
rewrite invrK.
rewrite mulNr.
rewrite (mulrC 7).
rewrite -(mulrA _ 7).
rewrite (mulrC 7).
rewrite (mulrDl _ _ 7).
rewrite -(mulrA _ (inv 7)).
rewrite (mulrC (inv 7) 2).
rewrite -(mulrA _ (2/7)).
rewrite -(mulrA _ (inv 7) 7).
rewrite mulVr;  [ | rewrite unitfE; lra ].
rewrite mulr1.
rewrite -(mulrA s3).
rewrite invrM;   [ | rewrite unitfE; lra ..].
rewrite -(mulrA _ (inv s3)).
rewrite (mulrDl _ _ 2).
rewrite addrC.
rewrite addrA.
set e := _ + (3*2).
rewrite (mulrDr (inv _)).
rewrite  mulNr mulrN.
rewrite (mulrC 2 s3) -(mulrA s3).
rewrite (mulrA _ s3).
rewrite mulVr;  [ | rewrite unitfE; lra ].
rewrite mul1r.
rewrite mulrC.
rewrite (mulrC _ e).
subst e.
rewrite (mulrDl _ _ (inv (2*4))).
rewrite !mulNr.
rewrite (addrC (- (_ * 7))).
rewrite (mulrC _ (inv(2*4))).
rewrite mulrA.
rewrite opprB.
subst RHS.
rewrite -(invf_div 6 5).
rewrite sqrtrV; [ | lra].
change (Num.sqrt _) with s3.
nra.
Qed.
(* end details *)

Lemma gauss_weight_4_1: gauss_weight _ _ _ _ (LR_roots legendre_roots_4) (@Ordinal 4 1 isT) = 
       1/2 + Num.sqrt(5/6)/6.
(* begin details: Proof.  ... very long and tedious ... Qed. *)
Proof.
set RHS := _ + _. simpl in RHS.
rewrite /gauss_weight /legendre_roots_4 /LR_roots /L /zeros_of_ortho_p /ROOTS_vals.
rewrite lagrangeE;  [ | Lia.lia | apply extend_roots_injective; apply lo_lt_hi ].
cbv zeta; expand_bigop.
  rewrite -/intgal ?r_ring /extend_roots /= ?r_ring. 
set s3 := Num.sqrt (6/5). simpl in s3.
set (b := Num.sqrt _).
set (c := Num.sqrt _). simpl in b,c.
rewrite polyCN opprK.
rewrite ?hornerE /=.
set a := inv _.
rewrite ?mulrD.
rewrite -?mulrA.
rewrite ?r_intgal ?r_ring.
rewrite ?(pull_left (polyC _)) ?r_intgal ?r_ring.
replace a with ( (((- c)%R + b)%E * ((- c - c) * (- c - b)))^-1 : R) by (subst a; f_equal; ring).
clear a; set a := inv _.
transitivity (a * ((- b * (2 / 3))%R + (- c * (2 / 3))%R + ((b * (2 / 3))%R + (b * (- c * (2 * - b)))%R))%E); [ ring |].
simpl in a.
unfold b,c in a.
assert (is_true (1 < s3)) by (rewrite -{1}sqrtr1 ltr_sqrt;  lra).
assert (s3<6/5). rewrite -(sqr_sqrt (6/5)) -/s3; try lra. nra.
assert (is_true (0 <= (3 - 2 * s3) / 7)) by nra.
rewrite mulrA ?mulrN ?mulNr ?mulrN.
rewrite -(mulrA c 2). rewrite (mulrA b c).
rewrite opprK.
rewrite (mulrC (b*c)) -(mulrA 2 b) (mulrA b b) sqr_sqrt; try lra.
rewrite ?(mulrDr a) ?mulrN.
set u := (a * (b * _)).
rewrite -(mulrC c).
rewrite !(mulrA _ _ (_ 7)).
rewrite (mulrDr c).
rewrite (mulrDr 2).
rewrite (mulrDr a).
rewrite !(mulrC 2 (c * _)).
rewrite -(mulrA c 3 2).
rewrite -(mulrA c (2 * s3)).
rewrite !(mulrA a c).
set (v := a*c).
match goal with |- (?x + ?z) + (?y + ?A) = RHS =>  transitivity (z + A) end.
ring.
clear u.
subst v a.
clear b.
subst c.
set c := (3 - 2*s3)/7.
set b := (3 + 2*s3)/7.
rewrite sub_mul2 ?mulNr ?mulrN.
rewrite opp_sub ?mulrN ?mulnR ?opprK ?mulrN.
rewrite ?mulrDr ?mulNr ?mulrN.
rewrite ?mulr1.
rewrite -?(mulrA 2).
rewrite sqr_sqrt; auto.
rewrite -sqrtrM; [ | subst c; lra].
rewrite ?(addrC (- _)).
rewrite ?(mulrA _ 2) ?(mulrC _ 2).
rewrite -?(mulrA 2 _ c).
rewrite ?(mulrDl _ _ c).
rewrite ?(mulrDr 2) ?mulrN ?mulNr ?mulrN.
rewrite ?(mulrDl (2*_) _ (Num.sqrt _)) ?mul1r.
set bcc := Num.sqrt b * c.
set ccc := Num.sqrt c * c.
rewrite -(mulrA 2 (Num.sqrt b) (Num.sqrt (c*b))).
rewrite -sqrtrM; [ | subst b; lra].
rewrite mulNr.
rewrite -(mulrA 2 (Num.sqrt c) (Num.sqrt (c*b))).
rewrite -sqrtrM; [ | subst c; lra].
rewrite (mulrA c c).
rewrite (mulrC (c*c)).
rewrite (@sqrtrM _ b (c*c)); [ | subst b; lra].
rewrite (@sqrtrM _ c c); auto.
rewrite sqr_sqrt; auto.
rewrite (mulrC b (c*b)) -(mulrA c b b).
rewrite (@sqrtrM _ c (b*b)); auto.
rewrite (@sqrtrM _ b b); [ | subst b; lra].
rewrite sqr_sqrt; [ | subst b; lra].
fold bcc.
set cbb := Num.sqrt c * b.
rewrite add_mul2.
rewrite add_mul2.
set u := (_ - _)+ (_ - _).
replace u with (2*(cbb-ccc)) by (subst u; lra).
clear u.
assert (cbb - ccc \is a unit). {
 rewrite unitfE.
 subst cbb ccc. clear bcc. rewrite -mulrBr.
apply mulf_neq0.
assert (c > 0). subst c; lra.
rewrite -sqrtr_gt0 in H2. lra.
subst b c. lra.
}
rewrite invrM; [  |  rewrite unitfE; lra | auto ].
set u := (cbb-ccc).
unfold cbb, ccc in u.
revert u.
rewrite -mulrBr. simpl.
rewrite invrM; [ | rewrite unitfE ..].
2:{ 
assert (c > 0). subst c; lra.
rewrite -sqrtr_gt0 in H3; lra.
}
2: subst b c; lra.
rewrite !mulrA.
rewrite (mulrC _ (inv 2)).
rewrite !mulrA.
rewrite mulVf; [ | lra].
rewrite mul1r.
rewrite (mulrC _ 3).
rewrite (mulrC _ (inv 3)).
rewrite (mulrC _ (inv 2)).
rewrite (mulrC _ s3).
rewrite  -!mulrA.
rewrite mulVf.
2: {
assert (c > 0). subst c; lra.
rewrite -sqrtr_gt0 in H3; lra. }
rewrite mulr1.
clear ccc cbb bcc H2. 
rewrite !mulrA.
subst b c.
revert RHS.
rewrite -(invrK (5/6)).
rewrite sqrtrV; [ |  lra].
rewrite invf_div.
change (Num.sqrt _) with s3.
intro.
rewrite (mulrC 3).
rewrite !(mulrC _ (inv 7)).
rewrite -?(mulrBr (inv 7)).
set u := (_ + _)- (_ - _).
replace u with (4 * s3)%R by (subst u; lra).
clear u.
rewrite mulrDr.
rewrite invrM; [ | rewrite unitfE; lra .. ].
rewrite -(mulrA s3 (inv 2)).
rewrite invrK.
rewrite mulVf; [ | lra]. rewrite mulr1.
rewrite (mulrC _ 7).
rewrite -(mulrA _ _ 3).
rewrite (mulrA (inv 7) 7).
rewrite mulVf; [ | lra].
rewrite mul1r.
rewrite (mulrC (s3 * 2)).
rewrite -(mulrA _ _ (s3*2)).
rewrite (mulrA _ 7).
rewrite mulVf; [ | lra].
rewrite mul1r.
rewrite invrM; [ | rewrite unitfE; lra ..].
rewrite (mulrC _ (inv 4)).
rewrite -(mulrA _ (inv s3) (_ * 2)).
rewrite (mulrC (inv 4) (_ * (_ * 2))).
rewrite mulrA.
rewrite mulVr.
2: rewrite unitfE; lra.
rewrite mul1r.
rewrite (addrC _ (2/4)).
rewrite -addrA.
subst RHS.
f_equal.
lra.
lra.
Qed.
(* end details *)

Lemma gauss_weight_4_2: gauss_weight _ _ _ _ (LR_roots legendre_roots_4) (@Ordinal 4 2 isT) = 
       1/2 + Num.sqrt(5/6)/6.
(* begin details: make use of the gauss_weight_4_1 lemma, with appropriate adaptation *)
Proof.
rewrite -gauss_weight_4_1.
rewrite /gauss_weight /legendre_roots_4 /LR_roots /L /zeros_of_ortho_p /ROOTS_vals.
rewrite ?lagrangeE;  try Lia.lia ; [ | apply extend_roots_injective; apply lo_lt_hi .. ].
cbv zeta; repeat expand_bigop.
  rewrite /extend_roots /= ?r_ring.
set s3 := Num.sqrt (6/5). simpl in s3.
rewrite -/intgal.
set (b := Num.sqrt _).
set (c := Num.sqrt _). simpl in b,c.
rewrite ?hornerE /= ?opprK ?r_ring.
set a := inv _.
rewrite ?opp_sub ?mulrN ?mulNr ?opprK.
set a' := inv _.
assert (a'=-a). subst a a'. rewrite -invrN. f_equal. ring.
rewrite H; clear H a'.
rewrite ?polyCN ?opprK ?add_mul2.
rewrite -?mulrA.
rewrite ?r_intgal.
rewrite ?mulrD ?mul_polyC' -?mulrA.
rewrite ?(pull_left (polyC _)) ?r_intgal ?r_ring.
ring.
Qed.
(* end details *)

Lemma gauss_weight_4_3: gauss_weight _ _ _ _ (LR_roots legendre_roots_4) (@Ordinal 4 3 isT) = 
       1/2 - Num.sqrt(5/6)/6.
(* begin details: make use of the gauss_weight_4_0 lemma, with appropriate adaptation *)
Proof.
rewrite -gauss_weight_4_0.
rewrite /gauss_weight /legendre_roots_4 /LR_roots /L /zeros_of_ortho_p /ROOTS_vals.
rewrite ?lagrangeE;  try Lia.lia ; [ | apply extend_roots_injective; apply lo_lt_hi .. ].
cbv zeta; repeat expand_bigop.
  rewrite /extend_roots /=  ?r_ring.
set s3 := Num.sqrt (6/5). simpl in s3.
rewrite ?opprK.
rewrite -/intgal ?r_intgal.
set (b := Num.sqrt _).
set (c := Num.sqrt _). simpl in b,c.
rewrite ?hornerE /= ?polyCN ?opprK ?r_ring.
set a := inv _.
set a' := inv _.
assert (a'=-a). subst a a'. rewrite -invrN. f_equal. ring.
rewrite H; clear H a'.
rewrite ?mulrD -?mulrA ?(pull_left (polyC _)) ?r_intgal ?r_ring.
ring.
Qed.
(* end details *)

Definition gauss_weights_4 : gauss_weights 4.
 apply (Build_gauss_weights legendre_roots_4
   [:: 1/2 - Num.sqrt(5/6)/6; 1/2 + Num.sqrt(5/6)/6; 1/2 + Num.sqrt(5/6)/6; 1/2 - Num.sqrt(5/6)/6]).
Proof.
intros.
ord_enum_cases i.
apply gauss_weight_4_0.
apply gauss_weight_4_1.
apply gauss_weight_4_2.
apply gauss_weight_4_3.
Defined.

(** ** Packaging together the packages *)

(** We will construct a sequence such that for any ordinal n in 'I_5,
  the ith element of the sequence is guaranteed to be the legendre_roots package for degree n,
  and a similar sequence for gauss_weights.  That guarantee will be enforced by 
  dependent types, so we first need to define the notion of a dependently typed list,
  where the nth element has type T(n).
*)

Inductive iseq (T: nat -> Type) : nat ->Type :=
| i_nil: iseq T O
| i_cons: forall i, T i -> iseq T i -> iseq T (S i).

Arguments i_nil {T}.
Arguments i_cons {T} [i].

Fixpoint nth_iseq [T: nat -> Type] [n: nat] (s: iseq T n) (i: 'I_n) {struct n} : T i.
(* begin details: A function to return the ith element of an iseq *)
destruct n; destruct i as [i Hi].
discriminate.
specialize (nth_iseq T n).
inversion s. subst i0.
simpl.
destruct (PeanoNat.Nat.eq_dec i n).
rewrite e; apply X.
assert (i<n)%N by abstract Lia.lia.
change i with (nat_of_ord (Ordinal H)).
apply nth_iseq. apply X0.
Defined.
(* end details *)

Declare Scope iseq_scope.
Delimit Scope iseq_scope with iseq.

Infix "::" := i_cons (at level 60, right associativity) : iseq_scope.

(** *** The legendre_roots packages up to degree 4 *)

Definition some_legendre_roots: iseq legendre_roots 5 := 
   (legendre_roots_4 
    :: legendre_roots_3
    :: legendre_roots_2 
    :: legendre_roots_1
    :: legendre_roots_0  
    :: i_nil )%iseq.

(** *** The gauss_weights packages up to degree 4 *)

Definition some_gauss_weights: iseq gauss_weights 5 := 
   (gauss_weights_4 
    :: gauss_weights_3
    :: gauss_weights_2 
    :: gauss_weights_1
    :: gauss_weights_0  
    :: i_nil )%iseq.

Lemma legendre_roots_unique: forall [n] (r r': legendre_roots n),
    r=r'.
(* begin details: Proof.  ... easy, by roots_of_ortho_p_unique ... Qed. *)
Proof.
intros.
destruct r as [f1 Hf1 roots1].
destruct r' as [f2 Hf2 roots2].
subst f1 f2.
f_equal.
apply roots_of_ortho_p_unique; auto with continuous.
apply lo_lt_hi.
Qed.
(* end details *)

(** *** Specialization of quadrature error to our instances for degrees up to 4 *)

 Definition Gauss_Legendre_quadrature (n: 'I_5):  (R -> R) -> R :=
  compute_G (nth_iseq some_gauss_weights n).

  Lemma legendre_quadrature_error': forall (n: 'I_5) (f: R->R),
   let GW := nth_iseq some_gauss_weights n in
      exists ξ:R, -1 <= ξ <= 1 /\
       ∫ f - Gauss_Legendre_quadrature n f =  
       derive1n (2*n+2) f ξ / 
        (factorial(2*n+2))%:R * ∫ (fun x => (horner (legendre n.+1) x)^2).
  Proof.
  intros. apply legendre_quadrature_error.
 Qed.

Locate "`|".

Definition quadrature_error_bound (f: R -> R) (n: 'I_5) (b: R) : Prop :=
    forall x: R, (-1 <= x <= 1)%R -> 
     `| (derive.derive1n (2*n+2) f x) | <= 
       b * ((factorial (2*n+2))%:R  / ∫ (fun x => (horner (legendre n.+1) x)^2)) .

Lemma quadrature_error_bound_is_bound:
  forall n f b,
   quadrature_error_bound f n b ->
     `|  ∫ f - Gauss_Legendre_quadrature n f | <= b.
Proof.
intros.
destruct (legendre_quadrature_error' n f) as [ξ [H1 H2]].
rewrite {}H2.
specialize (H _ H1).
set u := ∫ _ in H|-*.
assert (0 < u). {
  assert (H0 := sqr_poly_positive  _ _ lo_lt_hi w w_positive ltac:(auto with continuous)
    (legendre (nat_of_ord n).+1) (ortho_p_nonzero _ _ lo_lt_hi _ _)).
 rewrite hornerM' in H0; apply H0.
}
clearbody u. simpl in u.
set y := _ ξ in H|-*. clearbody y.
set g := (2 * nat_of_ord n + 2)%N in H|-*. clearbody g.
pose proof (fact_gt0 g).
set h := g`! in H,H2|-*. clearbody h. clear g ξ H1.
assert (0 < h%:R :> R) by (destruct h; try discriminate; apply ltr0Sn).
clear H2. simpl in H1.
rewrite -mulrA (mulrC _ u).
pose proof (divr_gt0 H0 H1).
rewrite (_: b = b * (u / h%:R) * (h%:R / u)).
 2: rewrite -mulrA -(invf_div u h%:R) divff; lra.
rewrite -(mulrA _ (u / _)).
rewrite (mulrC (u / _)).
rewrite (mulrA _ (_/u)).
rewrite ler_norml. rewrite ler_norml in H.
nra.
Qed.

End R.

End Legendre.



