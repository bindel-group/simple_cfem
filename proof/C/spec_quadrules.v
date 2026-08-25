(** * CFEM.C.spec_quadrules:  VST function specification for quadrules *)

(* begin details : Require Imports and Open Scope, etc. *)
Require Import VST.floyd.proofauto.
From CFEM.C Require Import quadrules.
From vcfloat Require Import FPStdCompCert FPStdLib.
Require Import Coq.Classes.RelationClasses.


From mathcomp Require (*Import*) ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require (*Import*) fintype finfun bigop finset fingroup perm order.
From mathcomp Require (*Import*) div ssralg countalg finalg zmodp matrix.
From mathcomp.zify Require Import ssrZ zify.
Import fintype matrix.

Require LAProof.accuracy_proofs.export.
Module F := LAProof.accuracy_proofs.mv_mathcomp.F.

(** Now we undo all the settings that mathcomp has modified *)
Unset Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import CFEM.C.nonexpansive.

Open Scope logic.

(* end details *)

(** The C program has a local static array containing all these values in this order: *)

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

(** This separation logic predicate describes an array containing those gauss_points values,
   located at the C program's extern variable named gauss_pts. *)
Definition gauss_pts_pred (gv: globals) : mpred :=
   data_at Ers (tarray tdouble (Zlength gauss_pts_list)) 
          (map Vfloat gauss_pts_list)
         (gv _gauss_pts).

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

(** This separation logic predicate describes an array containing those gauss_weights values,
   located at the C program's extern variable named gauss_wts. *)

Definition gauss_wts_pred (gv: globals) : mpred :=
   data_at Ers (tarray tdouble (Zlength gauss_wts_list)) 
          (map Vfloat gauss_wts_list)
         (gv _gauss_wts).

(** ** Low-level specs *)
(** The C program's gauss_point function just returns an element from the array.
  This low-level spec says just that.  Below, the high-level spec will say that
   the floating-point value is actually appropriate. *)
Definition gauss_point_spec_lowlevel : ident * funspec :=
  DECLARE _gauss_point
  WITH npts: Z, i: Z, gv: globals
  PRE [ tint, tint ]
    PROP((0 <= i < npts)%Z; (1 <= npts <= 10)%Z)
    PARAMS( Vint (Int.repr i); Vint (Int.repr npts))
    GLOBALS (gv)
    SEP( gauss_pts_pred gv )
  POST[ tdouble]
    PROP( )
    RETURN (Vfloat (Znth (npts*(npts-1)/2+i) gauss_pts_list))
    SEP( gauss_pts_pred gv ).

(** The C program's gauss_weight function just returns an element from the array.
  This low-level spec says just that.  Below, the high-level spec will say that
   the floating-point value is actually appropriate. *)
Definition gauss_weight_spec_lowlevel : ident * funspec :=
  DECLARE _gauss_weight
  WITH npts: Z, i: Z, gv: globals
  PRE [ tint, tint ]
    PROP((0 <= i < npts)%Z; (1 <= npts <= 10)%Z)
    PARAMS( Vint (Int.repr i); Vint (Int.repr npts))
    GLOBALS (gv)
    SEP( gauss_wts_pred gv )
  POST[ tdouble]
    PROP( )
    RETURN (Vfloat (Znth (npts*(npts-1)/2+i) gauss_wts_list))
    SEP( gauss_wts_pred gv ).

(** This function computes integer square roots by case analysis. *) 
Definition gauss2d_npoint1d_spec : ident * funspec :=
  DECLARE _gauss2d_npoint1d
  WITH s: Z
  PRE [ tint ]
    PROP(1 <= s <= 5)
    PARAMS( Vint (Int.repr (s*s)))
    SEP( )
  POST[ tint ]
    PROP( )
    RETURN (Vint (Int.repr s))
    SEP( ).

(** ** High-level specs *)

(** The high-level specifications of gauss_points() and gauss_weights()
  are based on the theory of Gauss-Legendre quadrature, and then
  we need to prove that certain floating point numbers are accurate
  approximations of the real-valued Gauss points and weights, so 
  we import all the appropriate stuff now. *)

From CFEM Require Import quadrature quadrature2 quadmodel_accuracy.  Import Legendre.
Require Import Interval.Tactic.
From mathcomp Require Import Rstruct.
From Stdlib Require Import Reals.
Instance InhR : Inhabitant R := 0%R.


(** float x is near real r when it's no more than half an ulp away *)
Definition half_an_ulp : R := FPCore.default_rel (coretype_of_type Tdouble).

Definition float_near (r: R) (x: ftype Tdouble) :=
  (Rabs (FT2R x - r) <= Rabs (FT2R x) * half_an_ulp)%R.

(** The ith Gauss point of Legendre polyomial n *)
Definition ith_gauss_point [n: 'I_5] (i: 'I_n) : R :=
    (tuple.tnth (ROOTS_vals  Legendre.lo Legendre.hi Legendre.w n
                              (LR_roots _ (nth_iseq some_legendre_roots n))) i).

(** The ith Gauss weight of Legendre polyomial n *)
Definition ith_gauss_weight [n: 'I_5] (i: 'I_n) : R :=
 tuple.tnth (GW_vals _ (nth_iseq some_gauss_weights n)) i.

Definition gauss_weight_f [n: 'I_5] (i: 'I_n) := 
    Znth ((Z.of_nat n)*(Z.of_nat n - 1)/2 + Z.of_nat i) gauss_wts_list.

Definition gauss_point_f [n: 'I_5] (i: 'I_n) := 
    Znth ((Z.of_nat n)*(Z.of_nat n - 1)/2 + Z.of_nat i) gauss_pts_list.

Lemma gauss_points_acc: forall (n: 'I_5) (i: 'I_n),  float_near (ith_gauss_point i) (gauss_point_f i).
Proof.
intros [n Hn] [i Hi]; simpl in *.
destruct n as [ | [ | [ | [ | [ |] ]]]]; try lia;
destruct i as [ | [ | [ | [ | [ |] ]]]]; try lia;
red;
set (d := half_an_ulp); hnf in d; simpl in d; subst d;
unfold ith_gauss_point, gauss_point_f, tuple.tnth; simpl;
try change nmodule.Algebra.zero with 0%R;
repeat change (ssralg.GRing.mul ?A ?B) with (A*B)%R;
repeat change (nmodule.Algebra.opp ?A) with (- A)%R;
repeat change (nmodule.Algebra.add ?A ?B) with (A + B)%R;
try change (ssralg.GRing.one _) with 1%R;
repeat change (ssralg.GRing.inv ?A) with (/A)%R;
rewrite <- ?Rstruct.RsqrtE, <- ?Rstruct.INRE, ?Rminus_diag;
first [rewrite ?Rabs_R0; Lra.lra | interval with (i_prec(110%positive))].
Qed.

Lemma gauss_weights_acc: forall (n: 'I_5) (i: 'I_n),  float_near (ith_gauss_weight i) (gauss_weight_f i).
Proof.
intros [n Hn] [i Hi]; simpl in *.
destruct n as [ | [ | [ | [ | [ |] ]]]]; try lia;
destruct i as [ | [ | [ | [ | [ |] ]]]]; try lia;
red;
set (d := half_an_ulp); hnf in d; simpl in d; subst d;
unfold ith_gauss_weight, gauss_weight_f, tuple.tnth; simpl;
try change nmodule.Algebra.zero with 0%R;
repeat change (ssralg.GRing.mul ?A ?B) with (A*B)%R;
repeat change (nmodule.Algebra.opp ?A) with (- A)%R;
repeat change (nmodule.Algebra.add ?A ?B) with (A + B)%R;
try change (ssralg.GRing.one _) with 1%R;
repeat change (ssralg.GRing.inv ?A) with (/A)%R;
rewrite <- ?Rstruct.RsqrtE, <- ?Rstruct.INRE, ?Rminus_diag;
first [rewrite ?Rabs_R0; Lra.lra | interval with (i_prec(110%positive))].
Qed.

(** The high-level spec of the gauss_point function says that it returns
  a floating-point value that's as close as possible to the ith Gauss point
   of the nth Legendre polynomial, provided that n<5.  Note that the low-level
   spec is willing to return a number for n≤10, but the high-level spec
   has nothing to say beyond degree 4. *) 
Definition gauss_point_spec : ident * funspec :=
  DECLARE _gauss_point
  WITH X: { n: 'I_5 & 'I_n}, gv: globals
  PRE [ tint, tint ] let '(existT _ n i) := X in 
    PROP()
    PARAMS( Vint (Int.repr (Z.of_nat i)); Vint (Int.repr (Z.of_nat n)))
    GLOBALS (gv)
    SEP( gauss_pts_pred gv )
  POST[ tdouble] let '(existT _ n i) := X in 
    EX x: ftype Tdouble,
    PROP(float_near (ith_gauss_point i) x)
    RETURN (Vfloat x)
    SEP( gauss_pts_pred gv ).

(** Proof that the low-level spec implies the high-level spec *)
Lemma sub_gauss_point: funspec_sub (snd gauss_point_spec_lowlevel) (snd gauss_point_spec).
(* begin details: Proof. ... Qed. *)
Proof.
apply NDsubsume_subsume.
split; auto.
unfold snd.
hnf; intros.
split; auto. intros [[n [i Hi]] gv] [? ?]. Exists (Z.of_nat n, Z.of_nat i, gv) emp.
normalize.
set (x := Znth _ gauss_pts_list).
destruct n as [n Hn].
simpl nat_of_ord.
pose proof (@ssrnat.ltP n 5). rewrite Hn in H0.
inv H0.
simpl in Hi.
pose proof (@ssrnat.ltP i n). rewrite Hi in H0. inv H0.
unfold_for_go_lower; normalize. simpl; entailer!; intros.
split; [ | repeat split; auto; try lia].
entailer!.
rewrite <- H4. clear rho' H3 H4.
Exists x.
entailer!!.
apply gauss_points_acc.
Qed.
(* end details *)

(** The high-level spec of the gauss_weight function says that it returns
  a floating-point value that's as close as possible to the ith Gauss weight
   of the nth Legendre polynomial, provided that n<5.  *) 
Definition gauss_weight_spec : ident * funspec :=
  DECLARE _gauss_weight
  WITH X: { n: 'I_5 & 'I_n}, gv: globals
  PRE [ tint, tint ] let '(existT _ n i) := X in 
    PROP()
    PARAMS( Vint (Int.repr (Z.of_nat i)); Vint (Int.repr (Z.of_nat n)))
    GLOBALS (gv)
    SEP( gauss_wts_pred gv )
  POST[ tdouble] let '(existT _ n i) := X in 
    EX x: ftype Tdouble,
    PROP(float_near (ith_gauss_weight i) x)
    RETURN (Vfloat x)
    SEP( gauss_wts_pred gv ).

(** Proof that the low-level spec implies the high-level spec *)
Lemma sub_gauss_weight: funspec_sub (snd gauss_weight_spec_lowlevel) (snd gauss_weight_spec).
(* begin details: Proof. ... Qed. *)
Proof.
apply NDsubsume_subsume.
split; auto.
unfold snd.
hnf; intros.
split; auto. intros [[n [i Hi]] gv] [? ?]. Exists (Z.of_nat n, Z.of_nat i, gv) emp.
normalize.
set (x := Znth _ gauss_wts_list).
destruct n as [n Hn].
simpl nat_of_ord.
pose proof (@ssrnat.ltP n 5). rewrite Hn in H0.
inv H0.
simpl in Hi.
pose proof (@ssrnat.ltP i n). rewrite Hi in H0. inv H0.
unfold_for_go_lower; normalize. simpl; entailer!; intros.
split; [ | repeat split; auto; try lia].
entailer!.
rewrite <- H4. clear rho' H3 H4.
Exists x.
entailer!!.
apply gauss_weights_acc.
Qed.
(* end details *)

(** *** 2-dimensional gauss points and weights *)
 Definition gauss2d_point_spec : ident * funspec :=
  DECLARE _gauss2d_point
  WITH sh: share, p: val, X: {n: 'I_5 & 'I_n * 'I_n}, gv: globals
  PRE [ tptr tdouble, tint, tint ]  let '(existT _ n (x,y)) := X in
    PROP(writable_share sh)
    PARAMS(p; Vint (Int.repr (Z.of_nat (y*n+x)%nat)); Vint (Int.repr (Z.of_nat (n*n)%nat)))
    GLOBALS (gv)
    SEP(data_at_ sh (tarray tdouble 2) p; gauss_pts_pred gv )
  POST[ tvoid ]  let '(existT _ n (x,y)) := X in
    EX rx: ftype Tdouble, EX ry: ftype Tdouble,
    PROP(float_near (ith_gauss_point x) rx;
                 float_near (ith_gauss_point y) ry)
    RETURN ()
    SEP(data_at sh (tarray tdouble 2) [Vfloat rx; Vfloat ry] p; gauss_pts_pred gv).

 Definition gauss2d_weight_spec : ident * funspec :=
  DECLARE _gauss2d_weight
  WITH sh:share, X: {n: 'I_5 & 'I_n * 'I_n}, gv: globals
  PRE [ tint, tint ]  let '(existT _ n (x,y)) := X in
    PROP(writable_share sh)
    PARAMS(Vint (Int.repr (Z.of_nat (y*n+x)%nat)); Vint (Int.repr (Z.of_nat (n*n)%nat)))
    GLOBALS (gv)
    SEP(gauss_wts_pred gv )
  POST[ tdouble ]  let '(existT _ n (x,y)) := X in
    EX x': ftype Tdouble, EX y': ftype Tdouble,
    PROP(float_near (ith_gauss_weight x) x';
                 float_near (ith_gauss_weight y) y')
    RETURN ( Vfloat (x' * y')%F64)
    SEP(gauss_wts_pred gv).


(** *** The triangle: Hughes quadrature points and weights, low-level specs only*)
Definition hughes_points: list (R*R) := [ (1/2, 0); (1/2, 1/2); (0, 1/2) ]%R.

Definition hughes_point_spec: ident * funspec :=
  DECLARE _hughes_point
  WITH sh: share, p: val, i: 'I_3
  PRE [ tptr tdouble, tint, tint ]
    PROP(writable_share sh)
    PARAMS(p; Vint (Int.repr (Z.of_nat i)); Vint (Int.repr 3))
    SEP(data_at_ sh (tarray tdouble 2) p )
  POST[ tvoid ]
    EX x: ftype Tdouble, EX y: ftype Tdouble,
    PROP(Znth (Z.of_nat i) hughes_points = (FT2R x, FT2R y))
    RETURN ()
    SEP(data_at sh (tarray tdouble 2) [Vfloat x; Vfloat y] p).

Definition hughes_weight: R := 1/6.

 Definition hughes_weight_spec : ident * funspec :=
  DECLARE _gauss2d_weight
  WITH i: 'I_3
  PRE [ tint, tint ]
    PROP()
    PARAMS(Vint (Int.repr (Z.of_nat i)); Vint (Int.repr 3))
    SEP()
  POST[ tdouble ]
    EX w: ftype Tdouble,
    PROP(float_near hughes_weight w)
    RETURN ( Vfloat w )
    SEP().

(* 

  Lemma legendre_quadrature_error': forall (n: 'I_5) (f: R->R),
   let GW := nth_iseq some_gauss_weights n in
      exists ξ:R, -1 <= ξ <= 1 /\
       ∫ f - Gauss_Legendre_quadrature n f =  
       derive1n (2*n+2) f ξ / 
        (factorial(2*n+2))%:R * ∫ (fun x => (horner (legendre n.+1) x)^2).
*)

Definition realfun_spec (f: R -> R) (acc: R) : funspec :=
 WITH x: ftype Tdouble
 PRE [ tdouble ]
   PROP ((-1 <= FT2R x <= 1)%R)
   PARAMS (Vfloat x)
   SEP()
 POST [ tdouble ]
   EX y: ftype Tdouble,
   PROP ((Rabs (FT2R y - f (FT2R x)) <= acc)%R)
   RETURN (Vfloat y)
   SEP ().

Definition δ := FPCore.default_rel FPCore.Tdouble.
Definition testfun_spec : ident * funspec := 
 DECLARE _testfun
  (realfun_spec (fun x => (1/2)*(1-x)*(cos x))%R (5*δ)).

Definition floatfun_spec (f: ftype Tdouble -> ftype Tdouble) : funspec :=
 WITH x: ftype Tdouble
 PRE [ tdouble ]
   PROP ()
   PARAMS (Vfloat x)
   SEP()
 POST [ tdouble ]
   PROP ()
   RETURN (Vfloat (f x))
   SEP ().

(* Znth (npts*(npts-1)/2+i) gauss_wts_list *)

(*
From libValidSDP Require Import fsum_l2r binary64.

Check frnd binary64.
Check (fun x => FS_val (frnd binary64 x)).
Lemma prec_lt_emax: forall t, Datatypes.is_true (@flocq_float.prec (fprecp t) <? femax t).
Proof.
intros.
pose proof fprec_lt_femax t.
unfold flocq_float.prec.
unfold fprec in H.
apply Z.ltb_lt; auto.
Qed.

Definition fspec (t: type) := @flocq_float.flocq_float (fprecp t) (femax t) (fprec_gt_one _) (prec_lt_emax t).

Lemma format_FT2R: forall t  (x: ftype t), Datatypes.is_true (@flocq_float.format (fprecp t) (femax t) (FT2R x)).
Proof.
Admitted.  (* from LAProof.accuracy_proofs.libvalidsdp. *)

Definition mkFS (x: ftype Tdouble) : float_spec.FS (fspec Tdouble)  := 
   float_spec.Build_FS_of (format_FT2R _ x).

Import finfun.
Locate "_ ^ _".
Check (fun n (a: R^n) => mkFS (fsum_l2r (map mkFS a))).
About mkFS.
(*
Corollary fsum_l2r_reals_err' n (x : R^n) :
  (Rabs (\sum_i x i - fsum_l2r [ffun i => frnd (x i)])
   <= INR n * eps * (\sum_i Rabs (x i)) + (1 + INR n * eps) * INR n * eta)%Re.
*)

Lemma  fsum_l2r_reals_err' n (x : R^n) :
  (Rabs (\sum_i x i - fsum_l2r [ffun i => frnd (x i)])
   <= INR n * eps * (\sum_i Rabs (x i)) + (1 + INR n * eps) * INR n * eta)%Re.
*)

Definition integrate_model (n: 'I_5) (f: ftype Tdouble -> ftype Tdouble) : ftype Tdouble :=
  F.sum (fun i: 'I_n => BMULT (gauss_weight_f i) (f (gauss_point_f i))).



Definition integrate_spec_lowlevel : ident * funspec :=
 DECLARE _integrate
 WITH f: ftype Tdouble -> ftype Tdouble, p: val, n : 'I_5, gv: globals
 PRE [ tptr (Tfunction [tdouble] tdouble cc_default), tint ]
    PROP ()
    PARAMS ( p; Vint (Int.repr (Z.of_nat n)))
    GLOBALS (gv)
    SEP( gauss_pts_pred gv; gauss_wts_pred gv; func_ptr' (floatfun_spec f) p)
 POST [ tdouble ]
    PROP()
    RETURN (Vfloat (integrate_model n f))
    SEP( gauss_pts_pred gv; gauss_wts_pred gv; func_ptr' (floatfun_spec f) p).

Definition fun_acc (f: ftype Tdouble -> ftype Tdouble) (g: R -> R) (b: R) :=
  (forall x: ftype Tdouble, -1 <= FT2R x <= 1 -> Rabs (FT2R (f x) - g (FT2R x)) <= b)%R.

Definition fun_acc' (f g: R -> R) (b: R) :=
  (forall x: R, -1 <= x <= 1 -> Rabs (f x - g x) <= b)%R.


Definition integrate_spec : ident * funspec :=
 DECLARE _integrate
 WITH f: ftype Tdouble -> ftype Tdouble, g : R -> R, f_acc: R, d: R, p: val, n : 'I_5, b: R, gv: globals
 PRE [ tptr (Tfunction [tdouble] tdouble cc_default), tint ]
    PROP (quadrature_error_bound g n b; deriv_bound g d; fun_acc f g f_acc)
    PARAMS ( p; Vint (Int.repr (Z.of_nat n)))
    GLOBALS (gv)
    SEP( gauss_pts_pred gv; gauss_wts_pred gv; func_ptr' (floatfun_spec f) p)
 POST [ tdouble ]
    EX y: ftype Tdouble,
    PROP( (Rabs (FT2R y - intgal g) <= f_acc + INR n * 3 * d )%R)
    RETURN (Vfloat y)
    SEP( gauss_pts_pred gv; gauss_wts_pred gv; func_ptr' (floatfun_spec f) p).


From libValidSDP Require flocq_float.

Lemma prec_lt_emax (t: type) : Datatypes.is_true (@flocq_float.prec (fprecp t) <? femax t).
Proof.
pose proof fprec_lt_femax t.
apply Z.ltb_lt; auto.
Qed.

Definition fspec t := @flocq_float.flocq_float (fprecp t) (femax t) (fprec_gt_one _) (prec_lt_emax t).

Lemma sub_integrate: funspec_sub (snd integrate_spec_lowlevel) (snd integrate_spec).
(* begin details: Proof. ... Qed. *)
Proof.
apply NDsubsume_subsume.
split; auto.
unfold snd.
hnf; intros.
split; auto. intros [[[[[[[f g] f_acc] d] p] n] b] gv] [? ?].
simpl prop. Exists (f,p,n,gv) emp.
normalize.
inv H. inv H4. inv H5.
unfold_for_go_lower; normalize. simpl; entailer!; intros.
inv H.
Exists (integrate_model n f).
entailer!!.
From libValidSDP Require binary64.
(*
 pose (x := float_spec.FS binary64.binary64).
assert (x = ftype Tdouble).
subst x. unfold binary64.binary64. simpl. unfold bsn_infnan.fis.
unfold flocq_float.flocq_float. unfold float_spec.FS. simpl.
Search flocq_float.format.
Search float_spec.FS_of.

unfold flocq_float.format. unfold flocq_float.generic_format_pred.

 unfold float_spec.FS_of. simpl.
 simpl.
 simpl. simpl.
hnf in x.
*)
pose proof integrate_model_err (fspec Tdouble) n.
assert (float_spec.FS (fspec Tdouble) = ftype Tdouble).

Admitted.


(** Finally we build an Abstract Specification Interface (ASI) containing all the instantiated specs *)
Definition quadrules_ASI: funspecs :=
 [ gauss2d_npoint1d_spec;
   gauss_point_spec; gauss_weight_spec;
   gauss2d_point_spec; gauss2d_weight_spec;
   hughes_point_spec; hughes_weight_spec
  ].





