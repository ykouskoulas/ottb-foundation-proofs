Require Import Reals.
Require Import Coquelicot.Coquelicot.
Require Import Lra.
Require Import ttyp.
Import Lra.

(*
This structure represents a segment of a path traveling from point
a to point b, with x and y components pathx and pathy, which has
length D.
*)

(* arrivebounds is a record type that contains bounds representing the
arrival time at a specific point p in the reachable area *)
Record arrivebounds (p:pt) :=
  mktm { te : R ; tl : R ; boundorder : te <= tl}.

Definition te' {p:pt} (b:arrivebounds p) := te p b.
Definition tl' {p:pt} (b:arrivebounds p) := tl p b.

(* Assertion that time t is a legitimate arrival time for the vehicle
   to which these bounds apply *)
Definition tarrive {p:pt} (b : arrivebounds p) (t : R) :=
  te' b <= t <= tl' b.

(* Asserting that for two vehicles may collide at p *)
Definition collision_possibility {p:pt} (o i : arrivebounds p) (t : R) :=
  tarrive o t /\ tarrive i t.

Definition Wie {p:pt} (i o : arrivebounds p):= te' o <= te' i <= tl' o.
Definition Wil {p:pt} (i o : arrivebounds p):= te' o <= tl' i <= tl' o.
Definition Woe {p:pt} (i o : arrivebounds p):= te' i <= te' o <= tl' i.
Definition Wol {p:pt} (i o : arrivebounds p):= te' i <= tl' o <= tl' i.

Definition We {p:pt} (i o : arrivebounds p) := Wie i o \/ Woe i o.
Definition Wl {p:pt} (i o : arrivebounds p) := Wil i o \/ Wol i o.

Lemma Wil_possible_collision : forall {p:pt} (o i : arrivebounds p),
    Wil i o -> exists t, collision_possibility o i t.
Proof.
  intros. unfold collision_possibility.
  unfold Wil in H.
  destruct o, i. simpl in *.
  inversion_clear H.
  exists tl1. unfold tarrive. simpl.
  split; split; lra.
Qed.

Lemma Wie_possible_collision : forall {p:pt} (o i : arrivebounds p),
    Wie i o -> exists t, collision_possibility o i t.
Proof.
  intros. unfold collision_possibility.
  unfold Wie in H.
  destruct o, i. simpl in *.
  inversion_clear H.
  exists te1. unfold tarrive. simpl.
  split; split; lra.
Qed.

Lemma Wol_possible_collision : forall {p:pt} (o i : arrivebounds p),
    Wol i o -> exists t, collision_possibility o i t.
Proof.
  intros. unfold collision_possibility.
  unfold Wol in H.
  destruct o, i. simpl in *.
  inversion_clear H.
  exists tl0. unfold tarrive. simpl.
  split; split; lra.
Qed.

Lemma Woe_possible_collision : forall {p:pt} (o i : arrivebounds p),
    Woe i o -> exists t, collision_possibility o i t.
Proof.
  intros. unfold collision_possibility.
  unfold Woe in H.
  destruct o, i. simpl in *.
  inversion_clear H.
  exists te0. unfold tarrive. simpl.
  split; split; lra.
Qed.

Lemma We_possible_collision : forall {p:pt} (o i : arrivebounds p),
    We i o <-> exists t, collision_possibility o i t.
Proof.
  intros. unfold collision_possibility.
  destruct o,i. unfold We.
  simpl. split. intros. inversion_clear H.
  apply Wie_possible_collision; assumption.
  apply Woe_possible_collision; assumption.

  intros. inversion_clear H; inversion_clear H0.
  unfold tarrive in H,H1.
  unfold Wie, Woe. simpl in *.
  inversion_clear H.
  inversion_clear H1.

  generalize (Rle_dec te0 te1) as teordering. intros.
  inversion_clear teordering. left.
  generalize (Rle_dec te1 tl0) as tetlordering. intros.
  inversion_clear tetlordering. split; assumption.
  exfalso.
  apply Rnot_le_lt in H4. lra.

  apply Rnot_le_lt in H1.
  right. split. left. assumption.
  generalize (Rle_dec te0 tl1) as tetlordering. intros.
  inversion_clear tetlordering. assumption.

  exfalso.
  apply Rnot_le_lt in H4. lra.
Qed.

Lemma Wl_possible_collision : forall {p:pt} (o i : arrivebounds p),
    Wl i o <-> exists t, collision_possibility o i t.
Proof.
  intros. unfold collision_possibility.
  destruct o,i. unfold Wl.
  simpl. split. intros. inversion_clear H.
  apply Wil_possible_collision; assumption.
  apply Wol_possible_collision; assumption.

  intros. inversion_clear H; inversion_clear H0.
  unfold tarrive in H,H1.
  unfold Wil, Wol. simpl in *.
  inversion_clear H.
  inversion_clear H1.

  generalize (Rle_dec tl1 tl0) as tlordering. intros.
  inversion_clear tlordering. left.
  split. 
  generalize (Rle_dec te0 tl1) as tetlordering. intros.
  inversion_clear tetlordering. assumption.

  exfalso.
  apply Rnot_le_lt in H4. lra.

  assumption.
  apply Rnot_le_lt in H1.
  right. split. 
  generalize (Rle_dec te1 tl0) as tetlordering. intros.
  inversion_clear tetlordering. assumption.
  exfalso.
  apply Rnot_le_lt in H4. lra.

  left. assumption.
Qed.


Lemma W_possible_collision : forall {p:pt} (o i : arrivebounds p),
    We i o <-> Wl i o.
Proof.
  split; intros.
  apply Wl_possible_collision; apply We_possible_collision; assumption.
  apply We_possible_collision; apply Wl_possible_collision; assumption.
Qed.

Definition W {p:pt} (o i: arrivebounds p) := We o i.

