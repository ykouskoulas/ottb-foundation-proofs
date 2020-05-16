(* begin hide *)
Require Import Reals.
Require Import Coquelicot.Coquelicot.
Require Import Lra.
Require Import util.
Require Import atan2.

(* end hide *)
(**** One-turn-to-bearing dynamics  ****)

(**

A trajectory gives the vehicle's position as a function of time, while
a path gives a vehicle's position with a non time-based
parameterization.

Piecewise functions Jx and Jy describe the equations used for the
trajectories for one-turn-to-bearing dynamics. Hx and Hy are the
equations for the path.

For this paper, we parameterize our paths by distance. This gives us a
canonical parameterization that is unique, and also exposes an
important parameter in our problem.

Positions on a circular arc during the turn are

1. Represented by the arguments to trig functions

2. Given in radians

3. Position 0 = point on the arc where the tangent line has angle 0

Equations represent a left turn as distances increase.

The naming convention 'arc' indicates the turn in the path, and 'lin'
indicates the linear part of the path tangent to the initial turn

*)

(** 
r:R is the radius of the initial turn

θ₀:R is the vehicle's initial orientation

x₀:R is the initial x position

y₀:R is the initial y position

θc:R is the angle of the turn in radians as an offset

s:R->R is the horizontal speed of the vehicle during the encounter as
       a function of time

rtp:0<r*θc is a guarantee that signs match and about the bounds of θc

d:R is the distance traveled

The initial orientation is θ₀, orientation after the turn is θ₀+θc
 *)

(*
   Functions of ottb paths in terms of distance traveled are
   used to construct trajectories. 
*)
Definition Hxarc r θ₀ x₀ d := r*sin(d/r + θ₀) - r*sin(θ₀) + x₀.
Definition Hyarc r θ₀ y₀ d := - r*cos(d/r + θ₀) + r*cos(θ₀)+ y₀.

Definition Hxlin θ₀ x₀ d := d*cos(θ₀) + x₀.
Definition Hylin θ₀ y₀ d := d*sin(θ₀) + y₀.

(**
Time derivatives require information about speed during the encounter.
For these to represent time derivatives, the correct relationship must
hold between functions of speed and distance over time
i.e., d = RInt s 0 t 
*)

Definition Hxarc' r θ₀ d := cos(d/r+θ₀).
Definition Hyarc' r θ₀ d := sin(d/r+θ₀).

Definition Hxlin' θ₀ (d:R) := cos(θ₀).
Definition Hylin' θ₀ (d:R) := sin(θ₀).



Definition Hx (r θ₀ x₀ θc:R) (rtp : 0 < r*θc < Rabs r*2*PI) (d:R) :=
  extension_cont (Hxarc r θ₀ x₀)
                 (fun q => Hxlin (θ₀+θc) (Hxarc r θ₀ x₀ (r*θc)) (q-r*θc))
                 (r*θc) d.

Definition Hy (r θ₀ y₀ θc:R) (rtp : 0 < r*θc < Rabs r*2*PI) (d:R) :=
  extension_cont (Hyarc r θ₀ y₀)
                 (fun q => Hylin (θ₀+θc) (Hyarc r θ₀ y₀ (r*θc)) (q-r*θc))
                 (r*θc) d.

Definition Hx' (r θ₀ θc:R) (rtp : 0 < r*θc < Rabs r*2*PI) (d:R) :=
  extension_cont (Hxarc' r θ₀) (Hxlin' (θ₀+θc)) (r*θc) d.

Definition Hy' (r θ₀ θc:R) (rtp : 0 < r*θc < Rabs r*2*PI) (d:R) :=
  extension_cont (Hyarc' r θ₀) (Hylin' (θ₀+θc)) (r*θc) d.

(*
Given initial conditions and radius, these are expressions for the
center of the turning circle.  
*)
Definition Tcx r θ₀ x₀ := x₀ + r*cos(PI/2+θ₀).
Definition Tcy r θ₀ y₀ := y₀ + r*sin(PI/2+θ₀).

    

(*
Mutually exclusive predicates based on initial conditions and a
point (x₁,y₁) assumed to be on the one-turn-to-bearing path, whether
that point is part of the turning phase, or the straight phase of the
maneuver.
*)
Definition turning r θ₀ x₀ y₀ x₁ y₁:= 
  r² = (x₁ - (Tcx r θ₀ x₀))² + (y₁ - (Tcy r θ₀ y₀))².

Definition straight r θ₀ x₀ y₀ x₁ y₁:= 
  r² < (x₁ - (Tcx r θ₀ x₀))² + (y₁ - (Tcy r θ₀ y₀))².


(*

If the radius of the initial turn , 'r' is known, calcdθ provides a
simple expression that we can use as part of the calculation of
distance traveled between two points, when the two points are still on
the initial turn.

If the radius 'r' is not known, we must use calcθ₁ below.

Returns results within interval indicated:

calcdθ : R -> R -> R -> R -> R -> R -> R[-2PI, 2PI]

asin : TI -> R[-PI/2, PI/2]
 *)
(**
Negative change in angle is returned in the case of negative radii r.
Positive change in angle is returned in the case of positive radii r.
*)
(* begin hide *)
Definition calcdθ θ₀ x₀ y₀ x₁ y₁ r :=
  match (Rlt_dec 0 ((x₁ - x₀) * cos(θ₀) + (y₁ - y₀) * sin(θ₀))) with
  | left _ => 2*asin (TI_map ((sqrt ((x₁ - x₀)² + (y₁ - y₀)²))
                                /(2*r)))
  | right _ =>
    match (Rgt_dec 0 ((x₁ - x₀) * cos(θ₀) + (y₁ - y₀) * sin(θ₀))) with
    | left _ => Rabs r / r * PI +
                2*asin (TI_map ((sqrt ((x₁ - (x₀ - 2*r*sin θ₀))² +
                                      (y₁ - (y₀ + 2*r*cos θ₀))²))
                                  /(2*r)))
    | right _ =>
      match (Req_EM_T y₀ y₁), (Req_EM_T x₀ x₁) with
      | left _, left _ => 0
      | _, _ => Rabs r / r * PI
      end
    end
  end.
(* end hide *)

Definition calcθ₁ θ₀ x₀ y₀ x₁ y₁ :=
  2*(atan2 (-(x₁ - x₀)*sin θ₀ + (y₁ - y₀)* cos θ₀) (* y *)
           ((x₁ - x₀)*cos θ₀ + (y₁ - y₀)* sin θ₀)). (* x *)

(* begin hide *)

Definition cθ₁ θ₀ x₀ y₀ x₁ y₁ r :=
  match ((total_order_T (-(x₁ - x₀)*sin θ₀ + (y₁ - y₀)* cos θ₀) 0),
         (total_order_T ((x₁ - x₀)*cos θ₀ + (y₁ - y₀)* sin θ₀) 0)) with
  | (inleft (right _), inleft (left _)) => sign r * 2 * PI
  | _ => calcθ₁ θ₀ x₀ y₀ x₁ y₁
  end.


Lemma calctheta_rel1 : forall θ₀ x₀ y₀ x₁ y₁ r,
    (-(x₁ - x₀)*sin θ₀ + (y₁ - y₀)* cos θ₀) = 0 /\
    ((x₁ - x₀)*cos θ₀ + (y₁ - y₀)* sin θ₀) < 0 ->
    cθ₁ θ₀ x₀ y₀ x₁ y₁ r = sign r * 2 * PI.
Proof.
  intros *. intros [yeq0 xlt0].
  unfold cθ₁.
  destruct (total_order_T (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) 0).
  + destruct s.
    ++ exfalso. lra.
    ++ destruct (total_order_T ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) 0).
       +++ destruct s.
           ++++ reflexivity.
           ++++ exfalso. lra.
       +++ exfalso. lra.
  + exfalso. lra.
Qed.

Lemma calctheta_rel2 : forall θ₀ x₀ y₀ x₁ y₁ r,
    ~ ((-(x₁ - x₀)*sin θ₀ + (y₁ - y₀)* cos θ₀) = 0 /\
        ((x₁ - x₀)*cos θ₀ + (y₁ - y₀)* sin θ₀) < 0) ->
    cθ₁ θ₀ x₀ y₀ x₁ y₁ r = calcθ₁ θ₀ x₀ y₀ x₁ y₁.
Proof.
  intros *. intros notnx.
  unfold cθ₁.
  destruct (total_order_T (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) 0).
  + destruct s.
    ++ reflexivity.
    ++ destruct (total_order_T ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) 0).
       +++ destruct s.
           ++++ exfalso. apply notnx. split; assumption.
           ++++ reflexivity.
       +++ reflexivity.
  + reflexivity.
Qed.



      
Lemma calcth1_atan2_s :forall x₁ y₁,
    calcθ₁ 0 0 0 x₁ y₁ = 2 * atan2 y₁ x₁.
Proof.
  intros.
  unfold calcθ₁ in *. 
  assert (- (x₁ - 0) * sin 0 + (y₁ - 0) * cos 0 = y₁) as id.
  rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  assert ((x₁ - 0) * cos 0 + (y₁ - 0) * sin 0 = x₁) as id.
  rewrite sin_0, cos_0. field.
  rewrite id. clear id.
  reflexivity.
Qed.



Lemma calctheta_rel1_s : forall x₁ y₁ r,
    y₁ = 0 /\ x₁ < 0 ->
    cθ₁ 0 0 0 x₁ y₁ r = sign r * 2 * PI.
Proof.
  intros.
  apply calctheta_rel1.
  rewrite cos_0, sin_0, Rmult_0_r, Rmult_0_r, Rmult_1_r, Rplus_0_l,
          Rminus_0_r, Rminus_0_r, Rplus_0_r, Rmult_1_r.
  assumption.
Qed.


Lemma calctheta_rel2_s : forall x₁ y₁ r,
    ~ (y₁ = 0 /\ x₁ < 0) ->
    cθ₁ 0 0 0 x₁ y₁ r = calcθ₁ 0 0 0 x₁ y₁.
Proof.
  intros.
  apply calctheta_rel2.
  rewrite cos_0, sin_0, Rmult_0_r, Rmult_0_r, Rmult_1_r, Rplus_0_l,
          Rminus_0_r, Rminus_0_r, Rplus_0_r, Rmult_1_r.
  assumption.
Qed.


Lemma xaxis_or_not_s : forall x₁ y₁,
    (y₁ = 0 /\ x₁ < 0) \/ ~ (y₁ = 0 /\ x₁ < 0).
Proof.
  intros. lra.
Qed.



(*

Conditions for path existence:
(0 <= θc <= PI -> 
(y₁ - y₀) * cos(θ₀) > (x₁ - x₀) * sin(θ₀) /\
(y₁ - y₀) * cos(θ₀+θc) <= (x₁ - x₀) * sin(θ₀+θc)) /\
(PI < θc < 2*PI -> 
((y₁ - y₀) * cos(θ₀) > (x₁ - x₀) * sin(θ₀) /\
 (y₁ - y₀) * cos(θ₀+PI) <= (x₁ - x₀) * sin(θ₀+PI)) \/
((y₁ - y₀) * cos(θ₀+PI) > (x₁ - x₀) * sin(θ₀+PI) /\
 (y₁ - y₀) * cos(θ₀+θc) <= (x₁ - x₀) * sin(θ₀+θc)))

*)


Definition calcL r θ₀ x₀ y₀ x₁ y₁ θc :=
  match Req_EM_T 0 (cos(θ₀+θc)) with
  | left _ => (* cos _ = 0 ; use sin _ version*)
    (y₁ - Hyarc r θ₀ y₀ (r*θc))
      / sin(θ₀+θc)
  | _ =>
    (x₁ - Hxarc r θ₀ x₀ (r*θc))
      / cos(θ₀+θc)
  end.
(* end hide *)

Definition calcL' r θ₀ x₀ y₀ x₁ y₁ θc :=
  sqrt ( (y₁ - Hyarc r θ₀ y₀ (r * θc))² + (x₁ - Hxarc r θ₀ x₀ (r * θc))²).

(*
Given r derivation
L = (x₁ - (r * sin (r * θc / r + θ₀) - r * sin θ₀ + x₀)) / cos (θ₀ + θc)
L = (y₁ - (- r * cos (r * θc / r + θ₀) + r * cos θ₀ + y₀)) / sin (θ₀ + θc)
solve for r

(x₁ - (r * sin (r * θc / r + θ₀) - r * sin θ₀ + x₀)) / cos (θ₀ + θc) = 
(y₁ - (- r * cos (r * θc / r + θ₀) + r * cos θ₀ + y₀)) / sin (θ₀ + θc)

(x₁ - r * sin (r * θc / r + θ₀) + r * sin θ₀ - x₀) * sin (θ₀ + θc) = 
(y₁ + r * cos (r * θc / r + θ₀) - r * cos θ₀ - y₀) * cos (θ₀ + θc)

((x₁ - x₀) * sin (θ₀ + θc) - r * (sin (θc + θ₀) * sin (θ₀ + θc) - sin θ₀ * sin (θ₀ + θc)) )  = 
((y₁ - y₀) * cos (θ₀ + θc) + r * (cos (θc + θ₀) * cos (θ₀ + θc) - cos θ₀ * cos (θ₀ + θc)) )

(x₁ - x₀) * sin (θ₀ + θc) - (y₁ - y₀) * cos (θ₀ + θc) = 
r * ( sin (θc + θ₀) * sin (θ₀ + θc) + cos (θc + θ₀) * cos (θ₀ + θc)
    - (cos θ₀ * cos (θ₀ + θc) + sin θ₀ * sin (θ₀ + θc)) )

(x₁ - x₀) * sin (θ₀ + θc) - (y₁ - y₀) * cos (θ₀ + θc) = 
r * ( 1 - cos θc )

 *)


Record pt := mkpt { ptx : R ; pty : R}.

Definition magnitude (p q : R->R) :=
  (comp sqrt (plus_fct (comp Rsqr p)
                       (comp Rsqr q))).

Record path_segment (D : nonnegreal) (pathx pathy : R->R) (a b:pt) :=
  path_intro {
      contx : (forall (d:R), continuous pathx d);
      conty : (forall (d:R), continuous pathy d);
      abnd : (mkpt (pathx 0) (pathy 0)) = a;
      bbnd : (mkpt (pathx D) (pathy D)) = b;
      pzbydist : forall d, 0 <= d ->
          is_RInt (magnitude (Derive pathx) (Derive pathy))
                  0 d d;
    }.

(* begin hide *)

Definition evalpath {D:nonnegreal} {Hx Hy : R-> R} {a b} 
           (p : path_segment D Hx Hy a b) (z:R) :=
  (mkpt (Hx z) (Hy z)).


(* Coercion xdom {p q : nonnegreal} (y : UI p) : UI q := UI_map q y. *)

Notation " '〚' p '〛(' z ')' " := (evalpath p z) (at level 100).



(* end hide *)
