Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.Arith.Lt.
Require Import Coq.Arith.Minus.
Require Import Coq.QArith.QArith_base.
Require Import Coq.QArith.Qround.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Classical.

Require Export Definitions.

(*
    Welcome to File #2 of Amanda's project!

    Here, we will define and admit a few lemmas.

    These concepts were found in the paper linked in Definitions.v

    2 of these are not admitted! Go to inscribedangle.v to see opposite_angles_equal
    and inscribed_angle formal proofs.

*)

(* First, lets make some axioms about geometry *)

(* 
IDEA:
    when 2 lines intersect at right angles,
    the opposite angles are equal.
*)
Lemma opposite_angles_equal :
    forall (a b c d : point),
    (* If a, b, c form a right angle and b, c, d form a right angle,
       then a = d and they make a straight line of 180 degrees.
       Note that 180 degrees = 2 for us.
    *)
    let v_ab := vector b a in
    let v_bc := vector b c in
    let v_bd := vector b d in
    (* Note that dot products are 0 when the vectors are orthogonal (90 degrees) *)
    dot_product v_ab v_bc = 0 ->
    dot_product v_bc v_bd = 0 ->
    dot_product v_ab v_bd = 0 - dot_product v_bc v_bc.
Proof.
Admitted.

(* See Equation 2.6 in the paper linked in Definitions.v
   With c <= d < a, b/g > (a-d)/d
*)
Lemma angle_ratio_inequality :
    forall (a d : Q) (beta gamma : Q),
    (* ensure set up right *)
    0 < d ->
    d < a ->
    0 < beta ->
    0 < gamma ->
    beta / gamma > (a - d) / d.
Proof.
    (* This was admitted in the paper - it is a given *)
Admitted.

(*
    The next three ideas describe Retrograde motion's definition.
    As time goes on, planet moves Forwards -> Stops -> Backwards.

    These ideas are given from seeing that in some small delta, the
    planet does not move, using calculations found in Definitions.v,
    particularly, the apparent_motion function.

*)

(* 
If Apollonius condition satisfied, 
then at some point, planet stops moving (0).
*)
Lemma apollonius_condition :
    forall (params : motion_params),
    params.(deferent_radius) > 0 ->
    params.(epicycle_radius) > 0 ->
    params.(deferent_angular_velocity) > 0 ->
    params.(epicycle_angular_velocity) > 0 ->
    (* This must follow *)
    retrograde_condition params ->
    exists t : Q,
    forall delta : Q, 
        0 < delta -> delta < 1#100 ->
        apparent_motion params t (t + delta) = 0%Z.
Proof.
Admitted.

(* before going stationary, the planet is moving prograde (1) *)
Lemma forward_motion_before_stationary :
    forall (params : motion_params) (t_stationary : Q),
    params.(deferent_radius) > 0 ->
    params.(epicycle_radius) > 0 ->
    params.(deferent_angular_velocity) > 0 ->
    params.(epicycle_angular_velocity) > 0 ->
    retrograde_condition params ->
    (forall delta : Q, 0 < delta -> delta < 1#100 -> apparent_motion params t_stationary (t_stationary + delta) = 0%Z) ->
    exists delta : Q, 
        delta > 0 /\
        (* Delta is BEFORE t_stationary *)
        delta < t_stationary /\
        apparent_motion params (t_stationary - delta) t_stationary = 1%Z.
Proof.
Admitted.

(* after stationary, planet moves backwards (-1) *)
Lemma backward_motion_after_stationary :
    forall (params : motion_params) (t_stationary : Q),
    params.(deferent_radius) > 0 ->
    params.(epicycle_radius) > 0 ->
    params.(deferent_angular_velocity) > 0 ->
    params.(epicycle_angular_velocity) > 0 ->
    retrograde_condition params ->
    (forall delta : Q, 0 < delta -> delta < 1#100 -> apparent_motion params t_stationary (t_stationary + delta) = 0%Z) ->
    exists delta : Q, 
        delta > 0 /\
        apparent_motion params t_stationary (t_stationary + delta) = (-1)%Z.
Proof.
Admitted.