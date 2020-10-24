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

Lemma turningcond : forall x y r,
    turning r 0 0 0 x y -> 2 * r * y = x² + y².
Proof.
  intros * trn.
  unfold turning, Tcx, Tcy in trn.
  autorewrite with null in trn.
  rewrite Rsqr_minus in trn.
  lra.
Qed.

Lemma condturning : forall x y r,
    2 * r * y = x² + y² -> turning r 0 0 0 x y.
Proof.
  intros * trn.
  unfold turning, Tcx, Tcy.
  arn.
  rewrite Rsqr_minus.
  lra.
Qed.

Lemma straightcond : forall r x y,
    straight r 0 0 0 x y -> (2 * r * y < x² + y²).
Proof.
  intros *. intro phase.
  unfold straight, Tcy, Tcx in phase.
  rewrite Rplus_0_r, sin_PI2, cos_PI2, Rmult_0_r,
  Rplus_0_l, Rplus_0_l, Rminus_0_r, Rmult_1_r in phase.
  rewrite Rsqr_minus in phase.
  apply (Rplus_lt_compat_r (-r²)) in phase.
  apply Rminus_gt_0_lt.
  setl (r² + - r²). setr (x² + (y² + r² - 2 * y * r) + - r²).
  assumption.
Qed.

Lemma condstraight : forall r x y,
    (2 * r * y < x² + y²) -> straight r 0 0 0 x y.
Proof.
  intros.
  unfold straight, Tcy, Tcx.
  rewrite Rplus_0_r, sin_PI2, cos_PI2, Rmult_0_r,
  Rplus_0_l, Rplus_0_l, Rminus_0_r, Rmult_1_r.
  rewrite Rsqr_minus.
  apply (Rplus_lt_reg_r (-r²)).
  setl 0. setr (x² + y² - 2 * y * r).
  lra.
Qed.

Lemma tscond : forall x y r,
    turning r 0 0 0 x y \/ straight r 0 0 0 x y ->
    2 * r * y <= x² + y².
Proof.
  intros * [trn | str].
  apply turningcond in trn; right; assumption.
  apply straightcond in str; left; assumption.
Qed.

Lemma straight_rot : forall r θ₀ x₀ y₀ x₁ y₁,
    straight r θ₀ x₀ y₀ x₁ y₁ ->
    straight r 0 0 0 ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)
             (- (x₁-x₀)* sin θ₀ + (y₁-y₀)*cos θ₀).
Proof.
  intros *. intro strt.

  unfold straight, Tcx, Tcy in *.
  autorewrite with null.

  assert (x₁ - (x₀ + r * cos (PI / 2 + θ₀)) =
          ((x₁ - x₀) + r * - cos (PI / 2 + θ₀))) as id. field.
  rewrite id in strt. clear id.
  assert (y₁ - (y₀ + r * sin (PI / 2 + θ₀)) =
          ((y₁ - y₀) - r * sin (PI / 2 + θ₀))) as id. field.
  rewrite id in strt. clear id.
  rewrite <- cos_sin, <- sin_cos in strt.
  rewrite Rsqr_plus, (Rsqr_minus (y₁ - y₀)) in strt.
  fieldrewrite ((- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀ - r))
               ((- (x₁ - x₀) * sin θ₀) + ((y₁ - y₀) * cos θ₀ - r)).
  rewrite Rsqr_plus.
  rewrite Rsqr_plus.
  fieldrewrite (((x₁ - x₀) * cos θ₀)² + ((y₁ - y₀) * sin θ₀)² +
                2 * ((x₁ - x₀) * cos θ₀) * ((y₁ - y₀) * sin θ₀) +
                ((- (x₁ - x₀) * sin θ₀)² + ((y₁ - y₀) * cos θ₀ - r)² +
                 2 * (- (x₁ - x₀) * sin θ₀) * ((y₁ - y₀) * cos θ₀ - r)))
               ((x₁ - x₀)² * ((sin θ₀)² + (cos θ₀)²) +
                (y₁ - y₀)² * ((sin θ₀)² + (cos θ₀)²) +
                r² +
                2 * r * ((x₁ - x₀) * sin θ₀ - (y₁ - y₀) * cos θ₀)
               ).
  rewrite sin2_cos2, Rmult_1_r, Rmult_1_r.
  rewrite <- (Rmult_1_r (r²)) at 2.
  rewrite <- (sin2_cos2 θ₀).
  setr ((x₁ - x₀)² + (r * sin θ₀)² + 2 * (x₁ - x₀) * (r * sin θ₀) +
        ((y₁ - y₀)² + (r * cos θ₀)² - 2 * (y₁ - y₀) * (r * cos θ₀))).
  assumption.
Qed.

Lemma rot_straight : forall r θ₀ x₀ y₀ x₁ y₁,
    straight r 0 0 0 ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)
             (- (x₁-x₀)* sin θ₀ + (y₁-y₀)*cos θ₀) ->
    straight r θ₀ x₀ y₀ x₁ y₁.
Proof.
    intros *. intro strt.

  unfold straight, Tcx, Tcy in *.
  autorewrite with null in *.

  assert (x₁ - (x₀ + r * cos (PI / 2 + θ₀)) =
          ((x₁ - x₀) + r * - cos (PI / 2 + θ₀))) as id. field.
  rewrite id. clear id.
  assert (y₁ - (y₀ + r * sin (PI / 2 + θ₀)) =
          ((y₁ - y₀) - r * sin (PI / 2 + θ₀))) as id. field.
  rewrite id. clear id.
  rewrite <- cos_sin, <- sin_cos.
  rewrite Rsqr_plus, (Rsqr_minus (y₁ - y₀)).
  assert ((- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀ - r)=
          (- (x₁ - x₀) * sin θ₀) + ((y₁ - y₀) * cos θ₀ - r)) as id; try lra.
  rewrite id in strt; clear id.
  rewrite Rsqr_plus in strt.
  rewrite Rsqr_plus in strt.
  assert (((x₁ - x₀) * cos θ₀)² + ((y₁ - y₀) * sin θ₀)² +
                2 * ((x₁ - x₀) * cos θ₀) * ((y₁ - y₀) * sin θ₀) +
                ((- (x₁ - x₀) * sin θ₀)² + ((y₁ - y₀) * cos θ₀ - r)² +
                 2 * (- (x₁ - x₀) * sin θ₀) * ((y₁ - y₀) * cos θ₀ - r)) = 
               ((x₁ - x₀)² * ((sin θ₀)² + (cos θ₀)²) +
                (y₁ - y₀)² * ((sin θ₀)² + (cos θ₀)²) +
                r² +
                2 * r * ((x₁ - x₀) * sin θ₀ - (y₁ - y₀) * cos θ₀)
               )) as id. unfold Rsqr. field. rewrite id in strt; clear id.
  rewrite sin2_cos2, Rmult_1_r, Rmult_1_r in strt.
  rewrite <- (Rmult_1_r (r²)) in strt at 2 .
  rewrite <- (sin2_cos2 θ₀) in strt.
  lrag strt.
Qed.


Lemma turning_rot : forall r θ₀ x₀ y₀ x₁ y₁,
    turning r θ₀ x₀ y₀ x₁ y₁ ->
    turning r 0 0 0 ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀).
Proof.
  intros * phase.
  unfold turning, Tcx, Tcy in *.
  autorewrite with null in *.
  rewrite <- cos_sin in phase.
  assert (x₁ - (x₀ + r * cos (PI / 2 + θ₀)) = x₁ - x₀ + r * - cos (PI / 2 + θ₀)) as id.
  field.
  rewrite id in phase.
  clear id.
  rewrite <- sin_cos in phase.
  rewrite phase. clear phase.
  repeat rewrite Rsqr_plus in *.
  repeat rewrite Rsqr_minus in *.
  repeat rewrite Rsqr_plus in *.
  
  setl ((x₁ - x₀)²
        + (y₁ - y₀)²
        + r² * ((sin θ₀)² + (cos θ₀)²)
        + 2 * (x₁ - x₀) * (r * sin θ₀)
        + (- 2 * (y₁ - y₀) * (r * cos θ₀))).
  setr ((x₁ - x₀)² * ((sin θ₀)² + (cos θ₀)²)
        + (y₁ - y₀)² * ((sin θ₀)² + (cos θ₀)²)
        + r²
          - 2 * (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) * r).
  repeat rewrite sin2_cos2.
  field.
Qed.

Lemma rot_turning : forall r θ₀ x₀ y₀ x₁ y₁,
    turning r 0 0 0 ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)
            (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) ->
    turning r θ₀ x₀ y₀ x₁ y₁.
Proof.
  intros * phase.
  unfold turning, Tcx, Tcy in *.
  autorewrite with null in *.
  rewrite <- cos_sin.
  assert (x₁ - (x₀ + r * cos (PI / 2 + θ₀)) = x₁ - x₀ + r * - cos (PI / 2 + θ₀)) as id.
  field.
  rewrite id.
  clear id.
  rewrite <- sin_cos.
  rewrite phase. clear phase.
  repeat rewrite Rsqr_plus in *.
  repeat rewrite Rsqr_minus in *.
  repeat rewrite Rsqr_plus in *.
  
  setr ((x₁ - x₀)²
        + (y₁ - y₀)²
        + r² * ((sin θ₀)² + (cos θ₀)²)
        + 2 * (x₁ - x₀) * (r * sin θ₀)
        + (- 2 * (y₁ - y₀) * (r * cos θ₀))).
  setl ((x₁ - x₀)² * ((sin θ₀)² + (cos θ₀)²)
        + (y₁ - y₀)² * ((sin θ₀)² + (cos θ₀)²)
        + r²
          - 2 * (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) * r).
  repeat rewrite sin2_cos2.
  field.
Qed.

(**

If the radius of the initial turn , 'r' is known, calcdθ provides a
simple expression that we can use as part of the calculation of
distance traveled between two points, when the two points are still on
the initial turn.

If the radius 'r' is not known, we must use calcθ₁ below.

Returns results within interval indicated:

calcdθ : R -> R -> R -> R -> R -> R -> R[-2PI, 2PI]

asin : TI -> R[-PI/2, PI/2]

Negative change in angle is returned in the case of negative radii r < 0.
Positive change in angle is returned in the case of positive radii 0 < r.

*)

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

Definition calcθ₁ θ₀ x₀ y₀ x₁ y₁ :=
  2*(atan2 (-(x₁ - x₀)*sin θ₀ + (y₁ - y₀)* cos θ₀) (* y *)
           ((x₁ - x₀)*cos θ₀ + (y₁ - y₀)* sin θ₀)). (* x *)


Lemma eqv_calcs : forall θ₀ x₀ y₀ x₁ y₁ r,
  let x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀) in
  let y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀) in
  forall (nO : ~(x = 0 /\ y = 0))
         (trn : turning r θ₀ x₀ y₀ x₁ y₁),
         calcθ₁ θ₀ x₀ y₀ x₁ y₁ = calcdθ θ₀ x₀ y₀ x₁ y₁ r.
Proof.
  intros * nO trn.
  unfold calcθ₁, calcdθ.
  unfold x in *; clear x.
  unfold y in *; clear y.
  apply turning_rot in trn.
  set (x := ((x₁ - x₀) * cos θ₀ + (y₁ - y₀) * sin θ₀)) in *. 
  set (y := (- (x₁ - x₀) * sin θ₀ + (y₁ - y₀) * cos θ₀)) in *. 
  apply turningcond in trn.

  destruct Rlt_dec.
  + assert ((x₁ - x₀)² + (y₁ - y₀)² = x² + y²) as sleql. {
      unfold x, y.
      repeat rewrite Rsqr_plus.
      repeat rewrite Rsqr_mult.
      set (dX := (x₁ - x₀)) in *.
      set (dY := (y₁ - y₀)) in *.
      repeat rewrite <- Rsqr_neg.
      setr (dY² * ((sin θ₀)²+(cos θ₀)²) +
            dX² * ((sin θ₀)²+(cos θ₀)²)).
      rewrite sin2_cos2.
      field. }
    rewrite sleql; clear sleql.
    apply Rmult_eq_compat_l.

    destruct (total_order_T 0 y); [destruct s|].
    ++ specialize (atan2Q1 _ _ r0 r1) as [at2l at2u].
       unfold asin, atan2 in *.
       destruct pre_atan2 as [p [[pl pu] [yd xd]]].
       destruct pre_asin as [q [[ql qu] sd]].
       specialize (posss _ _ nO) as zlt2.
       generalize zlt2; intro zlt3.
       apply sqrt_lt_1 in zlt2; try lra.
       rewrite sqrt_0 in zlt2.
       assert ((x² + y²) = sqrt (x² + y²) * sqrt (x² + y²)) as bu. {
         symmetry.
         apply sqrt_def; try lra. }
       
       assert (r = (x² + y²) / (2 * y)) as rd. {
         apply (Rmult_eq_reg_r (2 * y)); try lra.
         lrag trn. }
       rewrite bu in rd.
       rewrite rd in sd.
       assert ((sqrt (x² + y²) /
                     (2 * (sqrt (x² + y²) * sqrt (x² + y²) / (2 * y)))) =
               (y * / (sqrt (x² + y²)))) as id. {
         rewrite <- rd.
         apply (Rmult_eq_reg_r (2 * r * sqrt (x² + y²))).
         setl (sqrt (x² + y²) * sqrt (x² + y²)).
         intro req0.
         rewrite req0 in trn.
         autorewrite with null in trn.
         rewrite <- trn in zlt3.
         lra.
         setr (2 * r * y).
         change (sqrt (x² + y²) <> 0).
         lra.
         rewrite <- bu.
         symmetry.
         assumption.
         apply Rmult_integral_contrapositive_currified.
         apply Rmult_integral_contrapositive_currified.
         lra.
         intro req0.
         rewrite req0 in trn.
         autorewrite with null in trn.
         rewrite <- trn in zlt3.
         lra.
         intros seq0.
         rewrite seq0 in zlt2.
         lra. }
       rewrite id in sd.
       assert (sin p = y * / sqrt (y² + x²)) as id3. {
         apply (Rmult_eq_reg_r (sqrt (y² + x²))).
         setr y.
         change (sqrt (y² + x²) <> 0).
         rewrite Rplus_comm.
         intros x2d.
         rewrite x2d in zlt2.
         lra.
         symmetry.
         rewrite Rmult_comm.
         assumption.
         rewrite Rplus_comm.
         lra. }
       rewrite Rplus_comm in id3.
       rewrite <- id3 in sd.
       rewrite TI_Map_equiv_int in sd.
       2 : { apply SIN_bound. }
       clear - sd ql qu at2l at2u r0 r1.
       apply sin_injective_range; try lra.
    ++ rewrite <- e in *.
       autorewrite with null in *.
       symmetry in trn.
       unfold Rsqr in trn.
       apply Rmult_integral in trn; lra.
    ++ specialize (atan2Q4 _ _ r0 r1) as [at2l at2u].
       unfold asin, atan2 in *.
       destruct pre_atan2 as [p [[pl pu] [yd xd]]].
       destruct pre_asin as [q [[ql qu] sd]].
       specialize (posss _ _ nO) as zlt2.
       generalize zlt2; intro zlt3.
       apply sqrt_lt_1 in zlt2; try lra.
       rewrite sqrt_0 in zlt2.
       assert ((x² + y²) = sqrt (x² + y²) * sqrt (x² + y²)) as bu. {
         symmetry.
         apply sqrt_def; try lra. }
       
       assert (r = (x² + y²) / (2 * y)) as rd. {
         apply (Rmult_eq_reg_r (2 * y)); try lra.
         lrag trn. }
       rewrite bu in rd.
       rewrite rd in sd.
       assert ((sqrt (x² + y²) /
                     (2 * (sqrt (x² + y²) * sqrt (x² + y²) / (2 * y)))) =
               (y * / (sqrt (x² + y²)))) as id. {
         rewrite <- rd.
         apply (Rmult_eq_reg_r (2 * r * sqrt (x² + y²))).
         setl (sqrt (x² + y²) * sqrt (x² + y²)).
         intro req0.
         rewrite req0 in trn.
         autorewrite with null in trn.
         rewrite <- trn in zlt3.
         lra.
         setr (2 * r * y).
         change (sqrt (x² + y²) <> 0).
         lra.
         rewrite <- bu.
         symmetry.
         assumption.
         apply Rmult_integral_contrapositive_currified.
         apply Rmult_integral_contrapositive_currified.
         lra.
         intro req0.
         rewrite req0 in trn.
         autorewrite with null in trn.
         rewrite <- trn in zlt3.
         lra.
         intros seq0.
         rewrite seq0 in zlt2.
         lra. }
       rewrite id in sd.
       assert (sin p = y * / sqrt (y² + x²)) as id3. {
         apply (Rmult_eq_reg_r (sqrt (y² + x²))).
         setr y.
         change (sqrt (y² + x²) <> 0).
         rewrite Rplus_comm.
         intros x2d.
         rewrite x2d in zlt2.
         lra.
         symmetry.
         rewrite Rmult_comm.
         assumption.
         rewrite Rplus_comm.
         lra. }
       rewrite Rplus_comm in id3.
       rewrite <- id3 in sd.
       rewrite TI_Map_equiv_int in sd.
       2 : { apply SIN_bound. }
       clear - sd ql qu at2l at2u r0 r1.
       apply sin_injective_range; try lra.
  + apply Rnot_lt_le in n.
    destruct Rgt_dec.
    ++ clear n.
       
       assert ((x₁ - (x₀ - 2 * r * sin θ₀))² + (y₁ - (y₀ + 2 * r * cos θ₀))² =
               2 * r * (2 * r - y))
         as id. {
         repeat rewrite Rsqr_minus.
         repeat rewrite Rsqr_plus.
         setl ((x₁ - x₀)² + (y₁ - y₀)²
               + (2 * r)² * ((sin θ₀)² + (cos θ₀)²)
               + 2 * (x₁ - x₀) * 2 * r * sin θ₀
                 - 2 * (y₁ - y₀) * 2 * r * cos θ₀).
         rewrite sin2_cos2.
         set (dX := (x₁ - x₀)) in *.
         set (dY := (y₁ - y₀)) in *.
         setl (dX² + dY² + 2 * (2 * r² - (2 * r * (- dX * sin θ₀ + dY * cos θ₀)))).
         change (dX² + dY² + 2 * (2 * r² - 2 * r * y) = 2 * r * (2 * r - y)).
         rewrite trn.
         
         assert (x² + y² = dX² + dY²) as id2. {
           unfold x, y.
           repeat rewrite Rsqr_plus.
           repeat rewrite Rsqr_mult.
           setl (dY² * ((sin θ₀)² + (cos θ₀)²) +
                 dX² * ((sin θ₀)² + (cos θ₀)²)).
           rewrite sin2_cos2.
           field. }
         rewrite <- id2.
         setl (4 * r² - (x² + y²)).
         rewrite <- trn.
         setl (2 * r * (2 * r - y)).
         reflexivity. }
       rewrite id.

       destruct (total_order_T 0 y); [destruct s|].
       +++  specialize (atan2Q2 _ _ r0 r1) as [at2l at2u].
            unfold asin, atan2 in *.
            destruct pre_atan2 as [p [[pl pu] [yd xd]]].
            destruct pre_asin as [q [[ql qu] sd]].
            specialize (posss _ _ nO) as zlt2.
            generalize zlt2; intro zlt3.
            apply sqrt_lt_1 in zlt2; try lra.
            rewrite sqrt_0 in zlt2.
            assert ((x² + y²) = sqrt (x² + y²) * sqrt (x² + y²)) as bu. {
              symmetry.
              apply sqrt_def; try lra. }
            
            assert (r = (x² + y²) / (2 * y)) as rd. {
              apply (Rmult_eq_reg_r (2 * y)); try lra.
              lrag trn. }
            
            assert (0 < r) as zltr. {
              rewrite rd.
              apply (Rmult_lt_reg_r (2 * y)); try lra.
              lrag zlt3. }
            
            assert (Rabs r / r = 1) as id1. {
              rewrite Rabs_pos_eq; try lra.
              field; try lra. }
            rewrite id1.
            apply (Rmult_eq_reg_r (/2 )); try lra.
            setl p.
            setr (PI / 2 + q).
            
            rewrite sqrt_mult_alt in sd; try lra.
            rewrite <- (sqrt_square (2 * r)) in sd at 3; try lra.
            rewrite (sqrt_mult_alt (2 * r)) in sd; try lra.
            assert (sqrt (2 * r) * sqrt (2 * r - y) / (sqrt (2 * r) * sqrt (2 * r)) =
                    sqrt (1 - y / (2 * r))) as id3. {
              fieldrewrite (1 - y / (2 * r)) ((2 * r - y) / (2 * r)); try lra.
              rewrite sqrt_div_alt ; try lra.
              assert (sqrt (2 * r) <> 0) as sq2rne0. {
                rewrite sqrt_mult_alt; try lra.
                apply Rmult_integral_contrapositive_currified.
                intro sqrt2eq0.
                specialize (sqrt_lt_R0 2); lra.
                intro sqrtreq0.
                specialize (sqrt_lt_R0 r); lra. }
              apply (Rmult_eq_reg_r (sqrt (2 * r))); try lra.
              setl (sqrt (2 * r - y)); try assumption.
              setr (sqrt (2 * r - y)); try assumption.
              reflexivity. }
            rewrite id3 in sd; clear id3.
            assert (1 - y / (2 * r) = x² / (x² + y²)) as id4. {
              assert (1 = (x² + y²) / (x² + y²)) as one. {
                field. 
                lra. }
              rewrite one, rd; clear one.
              fieldrewrite (2 * ((x² + y²) / (2 * y)))
                           ((x² + y²) / y); try lra.
              rewrite <- pm.
              fieldrewrite (- (y / ((x² + y²) / y)))
                           (- y² / (x² + y²)).
              split; try lra.
              change (x² + y² <> 0); lra.
              setl (x² / (x² + y²)).
              change (x² + y² <> 0); lra.
              reflexivity. }
            rewrite id4 in sd; clear id4.
            rewrite sqrt_div in sd; try (apply Rle_0_sqr || assumption).
            rewrite Rsqr_neg in sd at 1.
            rewrite sqrt_Rsqr in sd; try lra.
            assert (- cos p = - x / sqrt (x² + y²)) as id5. {
              setr (- (x / sqrt (x² + y²))).
              change (sqrt (x² + y²) <> 0); lra.
              apply Ropp_eq_compat.
              apply (Rmult_eq_reg_r (sqrt (x² + y²))); try lra.
              setr x.
              change (sqrt (x² + y²) <> 0); lra.
              rewrite Rmult_comm.
              symmetry.
              rewrite Rplus_comm.
              assumption. }
            rewrite <- id5 in sd; clear id5.
            rewrite TI_Map_equiv_int in sd.
            2 : { specialize (COS_bound p) as [lb ub]; lra. }
            rewrite sin_cos in sd.
            symmetry in sd.
            apply cos_injective_range;
              try (split; lra).
            rewrite <- Ropp_involutive.
            rewrite <- (Ropp_involutive (cos p)).
            apply Ropp_eq_compat.
            assumption.
       +++ rewrite <- e in *.
           autorewrite with null in *.
           symmetry in trn.
           unfold Rsqr in trn.
           apply Rmult_integral in trn; lra.
       +++ specialize (atan2Q3 _ _ r0 r1) as [at2l at2u].
            unfold asin, atan2 in *.
            destruct pre_atan2 as [p [[pl pu] [yd xd]]].
            destruct pre_asin as [q [[ql qu] sd]].
            specialize (posss _ _ nO) as zlt2.
            generalize zlt2; intro zlt3.
            apply sqrt_lt_1 in zlt2; try lra.
            rewrite sqrt_0 in zlt2.
            assert ((x² + y²) = sqrt (x² + y²) * sqrt (x² + y²)) as bu. {
              symmetry.
              apply sqrt_def; try lra. }
            
            assert (r = (x² + y²) / (2 * y)) as rd. {
              apply (Rmult_eq_reg_r (2 * y)); try lra.
              lrag trn. }
            
            assert (r < 0) as zltr. {
              rewrite rd.
              apply (Rmult_lt_reg_r (- (2 * y))); try lra.
              setl (- (x² + y²)); try lra. }
            
            assert (Rabs r / r = - 1) as idn1. {
              unfold Rabs.
              destruct Rcase_abs; try lra.
              field; try lra. }
            rewrite idn1.
            apply (Rmult_eq_reg_r (/2 )); try lra.
            setl p.
            setr (- PI / 2 + q).

            assert (2 * r * (2 * r - y) = 2 * - r * (2 * - r + y)) as id5; try lra.
            rewrite id5 in sd; clear id5.
            
            rewrite sqrt_mult_alt in sd; try lra.
            assert (2 * r = - (2 * - r)) as id6; try lra.
            rewrite id6 in sd; clear id6.
            rewrite <- (sqrt_square (2 * - r)) in sd at 3; try lra.
            rewrite (sqrt_mult_alt (2 * - r)) in sd; try lra.
            assert (sqrt (2 * - r) * sqrt ((2 * - r) + y)
                                          / - (sqrt (2 * - r) * sqrt (2 * - r)) =
                    - sqrt (1 + y / (2 * - r))) as id3. {
              fieldrewrite (1 + y / (2 * - r)) ((2 * - r + y) / (2 * - r)); try lra.
              rewrite sqrt_div_alt ; try lra.
              assert (sqrt (2 * - r) <> 0) as sq2rne0. {
                rewrite sqrt_mult_alt; try lra.
                apply Rmult_integral_contrapositive_currified.
                intro sqrt2eq0.
                specialize (sqrt_lt_R0 2); lra.
                intro sqrtreq0.
                specialize (sqrt_lt_R0 (-r)); lra. }
              apply (Rmult_eq_reg_r (sqrt (2 * - r))); try lra.
              setl (- sqrt (2 * - r + y)); try assumption.
              setr (- sqrt (2 * - r + y)); try assumption.
              reflexivity. }
            rewrite id3 in sd; clear id3.
            assert (1 + y / (2 * - r) = x² / (x² + y²)) as id4. {
              assert (1 = (x² + y²) / (x² + y²)) as one. {
                field. 
                lra. }
              rewrite one, rd; clear one.
              fieldrewrite (2 * - ((x² + y²) / (2 * y)))
                           (- (x² + y²) / y); try lra.
              fieldrewrite ((y / (- (x² + y²) / y)))
                           (- y² / (x² + y²)).
              split; try lra.
              change (x² + y² <> 0); lra.
              setl (x² / (x² + y²)).
              change (x² + y² <> 0); lra.
              reflexivity. }
            rewrite id4 in sd; clear id4.
            rewrite sqrt_div in sd; try (apply Rle_0_sqr || assumption).
            rewrite Rsqr_neg in sd at 1.
            rewrite sqrt_Rsqr in sd; try lra.
            assert (cos p = (- (- x / sqrt (x² + y²)))) as id5. {
              setr (x / sqrt (x² + y²)).
              change (sqrt (x² + y²) <> 0); lra.
              apply (Rmult_eq_reg_r (sqrt (x² + y²))); try lra.
              setr x.
              change (sqrt (x² + y²) <> 0); lra.
              rewrite Rmult_comm.
              symmetry.
              rewrite Rplus_comm.
              assumption. }
            rewrite <- id5 in sd; clear id5.
            rewrite TI_Map_equiv_int in sd.
            2 : { specialize (COS_bound p) as [lb ub]; lra. }
            rewrite cos_sin in sd.
            symmetry in sd.
            apply (Rplus_eq_reg_l (PI/2)); try lra.
            setr q.
            apply sin_injective_range;
              try (split; lra).
            assumption.
    ++ destruct Req_EM_T.
       symmetry in e.
       apply Rminus_diag_eq in e.
       destruct Req_EM_T.
       symmetry in e0.
       apply Rminus_diag_eq in e0.
       exfalso.
       apply nO.
       unfold x, y.
       rewrite e, e0.
       arn.
       lra.
       unfold x, y in *.
       rewrite e in *.
       autorewrite with null in *.
       clear x y e.
       set (y := - (x₁ - x₀) * sin θ₀) in *.
       set (x := (x₁ - x₀) * cos θ₀) in *.
       apply Rnot_gt_le in n0.
       destruct n0 as [poof|zeqx]; try lra.
       destruct n as [poof|xeq0]; try lra.
       rewrite xeq0 in *.
       assert (~(y=0)) as nyeq0; try lra.
       assert (2 * r = y) as id. {
         apply (Rmult_eq_reg_r y); try lra.
         rewrite trn.
         unfold Rsqr.
         field. }
       destruct (total_order_T 0 y); [destruct s|].
       assert (0 < r) as rgt0; try lra.
       assert (Rabs r / r = 1) as id1. {
         rewrite Rabs_pos_eq; try lra.
         field; try lra. }
       rewrite id1.
       rewrite atan2_PI2; try assumption.
       field.
       lra.
       assert (r < 0) as rgt0; try lra.
       assert (Rabs r / r = - 1) as idn1. {
         unfold Rabs.
         destruct Rcase_abs; try lra.
         field; try lra. }
       rewrite idn1.
       rewrite atan2_mPI2; try assumption.
       field.

       apply Rnot_gt_le in n0.
       destruct n0 as [poof|zeqx]; try lra.
       destruct n as [poof|xeq0]; try lra.
       rewrite xeq0 in *.
       assert (~(y=0)) as nyeq0; try lra.
       assert (2 * r = y) as id. {
         apply (Rmult_eq_reg_r y); try lra.
         rewrite trn.
         unfold Rsqr.
         field. }
       destruct (total_order_T 0 y); [destruct s|].
       assert (0 < r) as rgt0; try lra.
       assert (Rabs r / r = 1) as id1. {
         rewrite Rabs_pos_eq; try lra.
         field; try lra. }
       rewrite id1.
       rewrite atan2_PI2; try assumption.
       field.
       lra.
       assert (r < 0) as rgt0; try lra.
       assert (Rabs r / r = - 1) as idn1. {
         unfold Rabs.
         destruct Rcase_abs; try lra.
         field; try lra. }
       rewrite idn1.
       rewrite atan2_mPI2; try assumption.
       field.
Qed.

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
