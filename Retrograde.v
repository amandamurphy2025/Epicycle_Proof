Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Classical_Prop.

Require Export Definitions.
Require Export Lemmas.

Require Import Lra.

(* 

    Welcome to File #4 of Amanda's project!

    Here we sum everything together!

    The basic idea of retrograde is proved, assuming the admitted lemmas.

    I think retrograde_example is a good place to look because it helps
    visualize what is happening here!

 *)

(* Here are some relations *)
Lemma Qlt_sub_iff : forall a b : Q, a - b < a <-> 0 < b.
Proof.
 (* I tried to prove these and got very confused with rational numbers *)
Admitted.

Lemma Qlt_add_iff : forall a b : Q, a < a + b <-> 0 < b.
Proof.
 (* I tried to prove these and got very confused with rational numbers *)
Admitted.

(* 
    If retrograde motion occurs (we see -1 and 1 at some given time intervals),
    Apollonius condition is satisfied. 
*)
Theorem necessary_condition_for_retrograde :
    forall (params : motion_params),
    params.(deferent_radius) > 0 ->
    params.(epicycle_radius) > 0 ->
    params.(deferent_angular_velocity) > 0 ->
    params.(epicycle_angular_velocity) > 0 ->
    (exists t1 t2 t3 : Q, 
        t1 < t2 /\ t2 < t3 /\
        apparent_motion params t1 t2 = 1%Z /\
        apparent_motion params t2 t3 = (-1)%Z) ->
        retrograde_condition params.
Proof.
    intros params.
    intros Hr_def_pos.
    intros Hr_epi_pos.
    intros Hw_def_pos.
    intros Hw_epi_pos.
    intros H_retrograde.
    destruct H_retrograde as [t1 [t2 [t3 [Ht1_lt_t2 [Ht2_lt_t3 [H_forward H_backward]]]]]].

    assert (H_stationary_exists: exists t_stat, t2 <= t_stat /\ t_stat <= t3 /\ forall delta, 0 < delta -> delta < 1#100 -> apparent_motion params t_stat (t_stat + delta) = 0%Z).
    { 
        (* 
            This assertion says there is some time where given a very small
            delta, that the planet appears stationary.
        *)
        admit. 
    }

    destruct H_stationary_exists as [t_stat [Ht2_le_tstat [Htstat_le_t3 H_stationary]]].

    assert (H_velocities_cancel: exists theta_def theta_epi, theta_def = params.(deferent_angular_velocity) * t_stat /\ theta_epi = params.(epicycle_angular_velocity) * t_stat /\ params.(deferent_radius) * params.(deferent_angular_velocity) * (rational_sin theta_def) = params.(epicycle_radius) * params.(epicycle_angular_velocity) * (rational_sin (theta_epi - theta_def))).
    { 
        (* 
            This assertion says that the velocities of the two
            (the deferent and the epicycle) are opposite of each other
            at time t_stat.  This makes sense intuitively, in order to see
            the planet not moving, the deferent and the epicycle must have 
            motion of the same velocity.
         *)
        admit. 
    }

    destruct H_velocities_cancel as [theta_def [theta_epi [Htheta_def [Htheta_epi H_cancel]]]].

    unfold retrograde_condition.

    (* Lets make this way more readable *)
    set (r_d := deferent_radius params).
    set (r_e := epicycle_radius params).
    set (w_d := deferent_angular_velocity params).
    set (w_e := epicycle_angular_velocity params).

    (* The next ideas are equations given in the paper. *)
    
    assert (H_sin_bound: exists theta, rational_sin theta >= rational_sin theta_def /\ rational_sin theta <= 1).
    { admit. }

    destruct H_sin_bound as [theta_max [H_sin_max_geq H_sin_max_leq]].

    assert (H_sin_epi_bound: rational_sin (theta_epi - theta_def) <= 1).
    { admit. }

    assert (H_max_velocity: r_d * w_d * rational_sin theta_max <= r_e * w_e).
    {
        (* max velocity from deferent <= max epicycle velocity *)
         admit. 
    }

    assert (H_velocity_ineq: r_d * w_d < r_e * w_e).
    { admit. }

    assert (H_ratio_ineq: w_e / w_d > r_d / r_e).
    {
        (* ratio of angular velocities MUST exceed ratio of radii *)
        admit.
    }

    (* This and the above are from equation 2.5 in the paper *)
    assert (H_radius_ineq: r_d / r_e > (r_d - r_e) / r_e).
    { admit. }

    (* 
        All these assertions are to say - the epicycle must be moving fast enough relative
        to the deferent to reverse the apparent motion
    *)

    apply Qlt_trans with ( y := r_d / r_e).
    -apply H_radius_ineq.
    -apply H_ratio_ineq.
Admitted.

(* If apollonius condition satisfied, retrograde motion will occur. *)
Theorem apollonius_condition_sufficient :
    forall (params : motion_params),
    params.(deferent_radius) > 0 ->
    params.(epicycle_radius) > 0 ->
    params.(deferent_angular_velocity) > 0 ->
    params.(epicycle_angular_velocity) > 0 ->
    retrograde_condition params ->
    exists t1 t2 t3 : Q,
        t1 < t2 /\ t2 < t3 /\
        apparent_motion params t1 t2 = 1%Z /\
        apparent_motion params t2 t3 = (-1)%Z.
Proof.
    intros params.
    intros Hr_def_pos.
    intros Hr_epi_pos.
    intros Hw_def_pos.
    intros Hw_epi_pos.
    intros H_retrograde.

    destruct (apollonius_condition params Hr_def_pos Hr_epi_pos Hw_def_pos Hw_epi_pos H_retrograde) as [t_stat H_stat].

    destruct (forward_motion_before_stationary params t_stat Hr_def_pos Hr_epi_pos Hw_def_pos Hw_epi_pos H_retrograde H_stat) as [delta1 [H_delta1_pos [H_delta1_small H_forward]]].

    destruct (backward_motion_after_stationary params t_stat Hr_def_pos Hr_epi_pos Hw_def_pos Hw_epi_pos H_retrograde H_stat) as [delta2 [H_delta2_pos H_backward]].

    (* the times! *)
    exists (t_stat - delta1), t_stat, (t_stat + delta2).
    split.
    {
        unfold Qlt.
        apply Qlt_sub_iff.
        apply H_delta1_pos.
    }
    {
        split.
        -apply Qlt_add_iff. apply H_delta2_pos.
        -split.
            +apply H_forward.
            +apply H_backward.
    }
Qed.

(* 
MAIN IDEA:
- apollonius condition <-> retrograde motion
*)
Theorem epicycles_produce_retrograde_motion :
    forall (params : motion_params),
    params.(deferent_radius) > 0 ->
    params.(epicycle_radius) > 0 ->
    params.(deferent_angular_velocity) > 0 ->
    params.(epicycle_angular_velocity) > 0 ->
    retrograde_condition params <->
    exists t1 t2 t3 : Q,
        t1 < t2 /\ t2 < t3 /\
        apparent_motion params t1 t2 = 1%Z /\
        apparent_motion params t2 t3 = (-1)%Z.
Proof.
    intros params.
    intros Hr_def_pos.
    intros Hr_epi_pos.
    intros Hw_def_pos.
    intros Hw_epi_pos.
    split.
        - apply apollonius_condition_sufficient.
            + apply Hr_def_pos.
            + apply Hr_epi_pos.
            + apply Hw_def_pos.
            + apply Hw_epi_pos.
        - apply necessary_condition_for_retrograde.
            + apply Hr_def_pos.
            + apply Hr_epi_pos.
            + apply Hw_def_pos.
            + apply Hw_epi_pos.
Qed.

(* Here are some parameters that work! *)
Example retrograde_example :
  let params := {|
    deferent_radius := 10;
    epicycle_radius := 3;
    deferent_angular_velocity := 1;
    epicycle_angular_velocity := 4
  |} in
  retrograde_condition params.
Proof.
    unfold retrograde_condition.
    simpl.
    replace (10 - 3) with 7 by reflexivity.
    unfold Qlt.
    simpl.
    reflexivity.
Qed.