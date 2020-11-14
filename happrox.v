(* begin hide *)
Require Import Reals.
Require Import Ranalysis5.
Require Import FunctionalExtensionality.
Require Import Coquelicot.Coquelicot.
Require Import Omega.
Require Import Lia.
Require Import Lra.
Require Import atan2.
Require Import ttyp.
Require Import tdyn.
Require Import util.
Require Import strt.
Require Import strt2.
Require Import tlens.
Require Import incr_function_le_ep.
Require Import dtlen.

Open Scope R_scope.
Set Bullet Behavior "Strict Subproofs".

Axiom path_length_lower_bound : forall pathx pathy s0 s1 d,
    is_RInt (magnitude (Derive pathx) (Derive pathy)) s0 s1 d ->
    sqrt ((pathx s0 - pathx s1)² + (pathy s0 - pathy s1)²) <= d.

(* could have different parameterizations; not all unit velocity *)
Axiom path_length_straight_line : forall pathx pathy s0 s1,
    is_RInt (magnitude (Derive pathx) (Derive pathy)) s0 s1
            (sqrt ((pathx s0 - pathx s1)² + (pathy s0 - pathy s1)²)) ->
    (exists v,
        forall s, s0 < s < s1 ->
                  0 <= v s /\
                  (Derive pathx s = (pathx s1 - pathx s0) * v s /\
                   Derive pathy s = (pathy s1 - pathy s0) * v s)).

(* infinite hat *)

Definition L x y θ r := r*θ + sqrt ((x-r*sin θ)² + (y-r*(1-cos θ))²).



Theorem underapprox_minlength_path_outer_tangent_infinite_hat_tile_std :
  forall r x y φ₂
         (p1p2 : 0 < φ₂)
         (p2ub : φ₂ <= 2 * PI)
         (lt : 0 < r)
         (oc : 2 * r * y < x² + y²),
    let wx := r*sin φ₂ in
    let wy := r*(1 - cos φ₂) in
    (y >= 0 /\ wx * y <= wy * x) -> 
    L x y 0 r  <= L x y (θ1 x y r) r.
Proof.
  intros until 4.
  intros * [rb lb].
  
  destruct (total_order_T 0 x) as [[zltx|zeq0]|zgtx].
  + unfold L.
    arn.
    

    apply condstraight in oc.
    specialize (Darm_Q_gen 0 0 0 x y r oc ltac:(lra)) as daqg.
    simpl in daqg.
    autorewrite with null in daqg.
    rewrite daqg.
    
  SearchPattern (_ - _ = 0).



Theorem underapprox_minlength_path_outer_tangent_infinite_hat_tile :
  forall r x y φ₁ φ₂
         (p1lb : 0 <= φ₁)
         (p1p2 : φ₁ < φ₂)
         (p2ub : φ₂ <= 2 * PI )
         (lt : 0 < r)
         (oc : 2 * r * y <= x² + y²),
    let mx := cos φ₁ in
    let my := sin φ₁ in
    let vx := r*sin φ₁ in
    let vy := r*(1 - cos φ₁) in
    let wx := r*sin φ₂ in
    let wy := r*(1 - cos φ₂) in
    (mx*(y - vy) >= my*(x - vx) /\
     (wx - vx)*(y - vy) <= (wy - vy)*(x - vx)) -> 
      L x y φ₁ r  <= L x y (θ1 x y r) r.
Proof.
  intros until 5.
  intros * [rb lb].

  destruct oc as [phase|phase].
  destruct rb as [gt |eq].
  + assert (sign (κ' x y r φ₁) = 1) as incr_k. {
      unfold κ', my, mx, vx, vy in *.
      apply (Rmult_gt_compat_l _ _ _ lt) in gt.
      assert (0 < - r * sin φ₁ * (x - r * sin φ₁) -
                  r * cos φ₁ * (- y + r * (1 - cos φ₁)))
        as P by lra.
      apply sign_eq_1 in P.
      rewrite sign_eq_pos_den; auto.
      apply posss; intros [P0 P1].
      apply Rminus_diag_uniq in P0;
        apply Rminus_diag_uniq in P1; subst; clear - phase.
      unfold Rsqr in phase.
      replace (r * sin φ₁ * (r * sin φ₁) +
               r * (1 - cos φ₁) * (r * (1 - cos φ₁))) with
          (r * r * (1 - 2 * cos φ₁ + ((sin φ₁)² + (cos φ₁)²)))
        in phase.
      { rewrite sin2_cos2 in phase; lra. }
      unfold Rsqr; ring.
    }

    
    phi1 <= k(x,y,phi1) <= (phi1+phi2)/2
    
    assert (φ₁ < θ1 x y r) as p1ltt1. {
(*
      k(phi1) = atan (y - vy) / (x - vx) = atan Yv/Xv
      k(phi2) = atan (y - wy) / (x - wx) = atan Yw/Xw

    (wx - vx) * (y - vy) <= (wy - vy) * (x - vx)
-----------------------------------
    (y - vy)/ (x - vx) ?<?>? (wy - vy)/(wx - vx)
                       ?<?>? (cos φ₁ -cos φ₂)/(sin φ₂ -sin φ₁)
                       ?<?>? tan ((φ₁ + φ₂)/2)
        k(φ₁)          ?<?>? (φ₁ + φ₂)/2






















-----------------------------------
    (y - vy)/ (x - vx) <= ((y - wy) - (y - vy))/ ((x - wx) - (x - vx))
    
    Yv/Xv <= (Yw - Yv)/(Xw - Xv)

    Yv/Xv <= 1/((Xw - Xv)/Yw) - 1/((Xw - Xv)/Yv)

    Yv/Xv <= 1/(Xw/Yw - Xv/Yw) - 1/(Xw/Yv - Xv/Yv)

    Yv/Xv <= 1/(1/(Yw/Xw) - Xv/Yw) - 1/(Xw/Yv - 1/(Yv/Xv))

*)
                                               clear lb.
      
Admitted.

Theorem underapprox_minlength_path_inner_tangent_infinite_hat_tile :
  forall r x y φ₁ φ₂ (p1p2 : φ₁ < φ₂ ) (lt : 0 < r),
    let nx := cos φ₂ in
    let ny := sin φ₂ in
    let vx := r*sin φ₁ in
    let vy := r*(1 - cos φ₁) in
    let wx := r*sin φ₂ in
    let wy := r*(1 - cos φ₂) in
    (nx*(y - wy) <= ny*(x - wx) /\ (wx - vx)*(y - vy) >= (wy - vy)*(x - vx)) -> 
      L x y φ₂ r  <= L x y (θ1 x y r) r.
Proof.
  intros until 2.
  intros * [lb rb].
Admitted.

