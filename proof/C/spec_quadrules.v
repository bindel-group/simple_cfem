(** * CFEM.C.spec_quadrules:  VST function specification for quadrules *)

(* begin details : Require Imports and Open Scope, etc. *)
Require Import VST.floyd.proofauto.
From vcfloat Require Import FPStdCompCert FPStdLib.
Require Import Coq.Classes.RelationClasses.
From CFEM Require Import C.nonexpansive quadrature quadrature2 quadmodel_accuracy.  
Import Legendre Quadmodel_F64.
Import fintype.  (* so we can use the 'I_5 notation *)

Set Bullet Behavior "Strict Subproofs".

From CFEM.C Require Import quadrules.
#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Open Scope logic.

(* end details *)

(** The C program has a local static array containing all these values in this order: *)

(** This separation logic predicate describes an array containing those gauss_points values,
   located at the C program's extern variable named gauss_pts. *)
Definition gauss_pts_pred (gv: globals) : mpred :=
   data_at Ers (tarray tdouble (Zlength gauss_pts_list)) 
          (map Vfloat gauss_pts_list)
         (gv _gauss_pts).

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
    RETURN (Vfloat (integrate_model_f Tdouble _ n (@gauss_point_f n) (@gauss_weight_f _) f))
    SEP( gauss_pts_pred gv; gauss_wts_pred gv; func_ptr' (floatfun_spec f) p).

(** ** High-level specs *)

(** The high-level specifications of gauss_points() and gauss_weights()
  are based on the theory of Gauss-Legendre quadrature, and then
  we need to prove that certain floating point numbers are accurate
  approximations of the real-valued Gauss points and weights, so 
  we import all the appropriate stuff now. *)

From mathcomp Require Import Rstruct.
(*From Stdlib Require*) Import Reals.

Instance InhR : Inhabitant R := 0%R.

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
    PROP(float_near (gauss_pt n i) x)
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
    PROP(float_near (gauss_wt n i) x)
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
  POST[ tvoid ]  let '(existT _ n (i,j)) := X in
    EX rx: ftype Tdouble, EX ry: ftype Tdouble,
    PROP(float_near (gauss_pt n i) rx;
                 float_near (gauss_pt n j) ry)
    RETURN ()
    SEP(data_at sh (tarray tdouble 2) [Vfloat rx; Vfloat ry] p; gauss_pts_pred gv).

 Definition gauss2d_weight_spec : ident * funspec :=
  DECLARE _gauss2d_weight
  WITH sh:share, X: {n: 'I_5 & 'I_n * 'I_n}, gv: globals
  PRE [ tint, tint ]  let '(existT _ n (i,j)) := X in
    PROP(writable_share sh)
    PARAMS(Vint (Int.repr (Z.of_nat (j*n+i)%nat)); Vint (Int.repr (Z.of_nat (n*n)%nat)))
    GLOBALS (gv)
    SEP(gauss_wts_pred gv )
  POST[ tdouble ]  let '(existT _ n (i,j)) := X in
    EX x': ftype Tdouble, EX y': ftype Tdouble,
    PROP(float_near (gauss_wt n i) x';
                 float_near (gauss_wt n j) y')
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

Definition integrate_spec : ident * funspec :=
 DECLARE _integrate
 WITH f: ftype Tdouble -> ftype Tdouble, g : R -> R, fb: R, f_acc: R, d: R, p: val, n : 'I_5, b: R, gv: globals
 PRE [ tptr (Tfunction [tdouble] tdouble cc_default), tint ]
    PROP (quadrature_error_bound g n b; 
                  fbound g fb; 
                  deriv_bound g d; 
                  function_accuracy Tdouble g f f_acc;
                  parameter_limits Tdouble n  fb f_acc)
    PARAMS ( p; Vint (Int.repr (Z.of_nat n)))
    GLOBALS (gv)
    SEP( gauss_pts_pred gv; gauss_wts_pred gv; func_ptr' (floatfun_spec f) p)
 POST [ tdouble ]
    EX y: ftype Tdouble,
    PROP( (Rabs (FT2R y - intgal g) <= integrate_model_acc Tdouble n fb d f_acc + b)%R)
    RETURN (Vfloat y)
    SEP( gauss_pts_pred gv; gauss_wts_pred gv; func_ptr' (floatfun_spec f) p).

Import Init.Datatypes.
From LAProof.accuracy_proofs Require Import preamble common dotprod_model sum_model.

Lemma sub_integrate: funspec_sub (snd integrate_spec_lowlevel) (snd integrate_spec).
(* begin details: Proof. ... Qed. *)
Proof.
apply NDsubsume_subsume.
split; auto.
unfold snd.
hnf; intros.
split; auto. intros [[[[[[[[f g] fb] f_acc] d] p] n] b] gv] [? ?].
simpl prop. Exists (f,p,n,gv) emp.
normalize.
inv H. inv H4. inv H5.
unfold_for_go_lower; normalize. simpl; entailer!; intros.
inv H.
match goal with H: Vfloat ?MODEL <> Vundef |- _ => Exists MODEL end.
entailer!!.
clear H9 H8 H7 x1 Pp p H3 H2 gv H7 g0.
eapply integrate_model_err; try eassumption.
intros; apply gauss_point_f_bound.
apply gauss_point_f_acc.
apply gauss_weight_f_acc.
apply gauss_weight_f_range.
Qed.

(** Finally we build an Abstract Specification Interface (ASI) containing all the instantiated specs *)
Definition quadrules_ASI: funspecs :=
 [ gauss2d_npoint1d_spec;
   gauss_point_spec; gauss_weight_spec;
   gauss2d_point_spec; gauss2d_weight_spec;
   hughes_point_spec; hughes_weight_spec
  ].





