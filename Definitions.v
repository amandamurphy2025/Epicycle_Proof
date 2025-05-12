Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.
Require Import Coq.Lists.List.
Import ListNotations.

(**
    WELCOME TO AMANDA'S PROJECT :D

        ~+

                 *       +
           '                  |
       ()    .-.,='``'=.    - o -
             '=/_       \     |
          *   |  '=._    |
               \     `=./`,        '
            .   '=.__.=' `='      *
   +                         +
        O      *        '       .

    This is a loosely followed formalization of a proof found here:
    https://digitalrepository.unm.edu/cgi/viewcontent.cgi?article=1001&context=math_etds

    except angles are difficult and irrational - so we are approximating them.

    The very general idea is that given the retrograde condition below, there exists
    intervals of times such that planet is stationary, moving prograde, and moving retrograde.

    This is hard!  I ended up focusing on more geometric ideas, and
    formally proved the inscribed angle theorem and
    that opposite angles are equal via a Euclidian definition.
     - See Lemmas.v for other proofs that were attempted and admitted :(
     - See inscribedangle.v for proofs that worked! :)

    
    In this file, I will be giving some definitions we
    will use throughout the rest of the project.

**)

(** 2D GEOMETRY **)

(* a point is a pair of rational numbers *)
Definition point := (Q * Q)%type.

(* a vector from one point to another *)
Definition vector (p1 p2 : point) : (Q * Q) :=
    let (x1, y1) := p1 in
    let (x2, y2) := p2 in
    (x2 - x1, y2 - y1).

(* Some operations on vectors *)
Definition dot_product (v1 v2 : Q * Q) : Q :=
    let (x1, y1) := v1 in
    let (x2, y2) := v2 in
    x1 * x2 + y1 * y2.

Definition magnitude_squared (v : Q * Q) : Q :=
    let (x, y) := v in
    x * x + y * y.

Definition distance_squared (p1 p2 : point) : Q :=
    magnitude_squared (vector p1 p2).

(** ASTRONOMY CONCEPTS **)

(* Earth is at the origin *)
Definition earth : point := (0, 0).

(* circle = a center point and a radius *)
Definition circle := (point * Q)%type.

(* The deferent is the big orbit circle *)
Definition deferent (center : point) (radius : Q) : circle :=
    (center, radius).

(* The epicycle is the smaller circle on the deferent *)
Definition epicycle (center : point) (radius : Q) : circle :=
    (center, radius).


(** TRIGONOMETRY **)

(* 
Trigonometry is hard, so we are doing a lot of hand waving
The idea is this is sort of like the quadrants of a x-y plane.
    - 1 = 90°
    - 2 = 180°
    - 3 = 270°
    - 4 = 360° or 0°

NOTE: this ended up not totally working - but you get the idea.
*)

Definition rational_cos (theta : Q) : Q :=
    let z_quadrant := Z.modulo (Qfloor theta) 4 in
    let t := theta - inject_Z (Qfloor theta) in  (* fractional part *)
    if Z.eqb z_quadrant 0 then 
        1 - t * t       (* Q1 *)
    else if Z.eqb z_quadrant 1 then 
        -t              (* Q2 *)
    else if Z.eqb z_quadrant 2 then 
        -1 + t * t      (* Q3 *)
    else 
        t - 1           (* Q4 *)
  .

(* silly sin based on cos *)
Definition rational_sin (theta : Q) : Q :=
    rational_cos (theta - 1).


(* Find position on circle from the angle *)
Definition position_on_circle (c : circle) (theta : Q) : point :=
    let (center, radius) := c in
    let (cx, cy) := center in
    (cx + radius * (rational_cos theta), cy + radius * (rational_sin theta)).


(** EPICYCLE MODEL **)

(* motion *)

(* This contains all information needed about epicyclic orbit *)
Record motion_params := {
    deferent_radius : Q;
    epicycle_radius : Q;
    deferent_angular_velocity : Q;
    epicycle_angular_velocity : Q
}.

(* 
This is important!!!!!
Retrograde motion occurs when the ratio of
angular velocity is bigger than some critical value
found from the radii.

Creds: Apollonius 200 BCE.
*)
Definition retrograde_condition (params : motion_params) : Prop :=
    params.(epicycle_angular_velocity) / params.(deferent_angular_velocity) > (params.(deferent_radius) - params.(epicycle_radius)) / params.(epicycle_radius).

(* positions in epicycle *)

(* Finds where the epicycle is located on the deferent *)
Definition epicycle_center_at_time (params : motion_params) (t : Q) : point :=
    let def_circle := deferent earth params.(deferent_radius) in
    let theta_def := params.(deferent_angular_velocity) * t in
    position_on_circle def_circle theta_def.

(* Finds where the planet is on the epicycle *)
Definition planet_position_at_time (params : motion_params) (t : Q) : point :=
    let epicycle_center := epicycle_center_at_time params t in
    let epi_circle := epicycle epicycle_center params.(epicycle_radius) in
    let theta_epi := params.(epicycle_angular_velocity) * t in
    position_on_circle epi_circle theta_epi.

(* observed motion from earth *)

(* Calculate angle from earth to planet (point) *)
Definition angle_from_earth (p : point) : Q :=
    let (x, y) := p in
    if Qeq_bool x 0 then
        (* when x = 0 *)
        if Qle_bool 0 y then 
            (* when y >= 0 *)
            inject_Z 1
        else 
            (* when y < 0 *)
            inject_Z 3
    else if Qle_bool 0 x then
    (* when x > 0 *)
        if Qle_bool 0 y then 
            (* When x > 0 and y > 0 *)
            (* Q1 *)
            (y / x) / (inject_Z 4)
        else 
            (* when x > 0 and y < 0 *)
            (* Q4 *)
            inject_Z 4 + (y / x) / (inject_Z 4)
    else
        (* when x < 0 *)
        (* Q2 and Q3 *)
        inject_Z 2 + (y / x) / (inject_Z 4).

(* 
Take 2 different angles (positions) and find direction of motion
 - prograde = 1 (forwards)
 - retrograde = -1 (backwards)
 - stationary = 0
*)
Definition apparent_motion_direction (angle1 angle2 : Q) : Z :=
    let diff := angle2 - angle1 in
    if Qle_bool diff (-1#10) then -1%Z (*retrograde*)
    else if Qle_bool (1#10) diff then 1%Z (*prograde*)
    else 0%Z. (*not moving*)

(* From 2 different times, find motion *)
Definition apparent_motion (params : motion_params) (t1 t2 : Q) : Z :=
  let pos1 := planet_position_at_time params t1 in
  let pos2 := planet_position_at_time params t2 in
  let angle1 := angle_from_earth pos1 in
  let angle2 := angle_from_earth pos2 in
  apparent_motion_direction angle1 angle2.

(* done with definitions! *)
