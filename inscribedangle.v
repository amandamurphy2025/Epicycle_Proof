Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qround.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Arith.Minus.
Require Import Coq.QArith.QArith_base.
Require Import Coq.QArith.Qabs.
Require Import Coq.QArith.Qround.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Classical.
Require Import Coq.QArith.QArith.
Require Import Coq.QArith.Qabs.
Require Import Coq.Arith.Lt.
Require Import Coq.Arith.Minus.
Require Import Coq.QArith.QArith_base.
Require Import Coq.QArith.Qround.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Logic.Classical.

Require Import NArith.
Require Import GeoCoq.Coinc.Utils.sets.
Require Import GeoCoq.Main.Meta_theory.Models.tarski_to_cong_theory.
Require Import GeoCoq.Coinc.CongR.

Require Import Coq.Reals.RIneq.
Require Import Coq.Reals.Reals.
Require Import GeoCoq.Main.Annexes.inscribed_angle.

Open Scope R_scope.

(**
    Welcome to File #3 of Amanda's Project.

    If you cannot tell by now, I got very confused and bogged down
    by rational / real numbers - but this is one way I got to work.

    We start by defining our own idea of points, angles, triangles, lines, etc.

    Then we play around with them!

    Below you will find
      - angle_lemma_detailed_proof
      - vertical_angles_equal
**)

Parameter Point : Type.
Parameter angle : Point -> Point -> Point -> R.

Parameter center : Point.
Parameter on_circle : Point -> Prop.

Axiom angle_comm : forall A B C, angle A B C = angle C B A.

Axiom angle_addition : forall A B C D,
    angle A B C + angle C B D = angle A B D.

Definition triangle (A B C : Point) :=
    A <> B /\ B <> C /\ C <> A.

Definition isosceles (A B C : Point) :=
    triangle A B C /\ angle B A C = angle C B A.

Axiom triangle_angle_sum : forall A B C,
    triangle A B C -> angle A B C + angle B C A + angle C A B = 180.

(* Axiom for initial proof try to simplify *)
Axiom inscribed_angle_theorem : forall A B D,
    on_circle A -> on_circle B -> on_circle D -> angle A D B = (1/2) * angle A center B.

Theorem central_angle_double_inscribed : forall A B D gamma,
    on_circle A -> on_circle B -> on_circle D ->
    angle A D B = gamma ->
    angle A center B = 2 * gamma.
Proof.
    (* Silly proof!  Using the axiom above. *)
    intros A B D gamma.
    intros HA HB HD.
    intros Hadb.

    assert (angle A D B = (1/2) * angle A center B).
    { 
        (* apply axiom *)
        apply inscribed_angle_theorem.
        { apply HA. }
        { apply HB. }
        { apply HD. }
    }

    rewrite Hadb in H.

    assert (2 * gamma = angle A center B) as Hg.
    {
        assert (2 * gamma = 2 * ((1/2) * angle A center B)) as H1.
        {
            rewrite H. reflexivity.
        }
        assert (2 * ((1/2) * angle A center B) = angle A center B) as H2.
        { field. }
        rewrite H2 in H1. exact H1.
    }

    symmetry. apply Hg.
Qed.

Require Import Coq.micromega.Psatz.

(* 
   Below are some silly things I had to prove for the sake of
   the proof working.
*)

Theorem algebraic_rearrangement : forall a b c d : R,
  a + (b + c) = d -> a = d - b - c.
Proof.
  intros a b c d H.
  unfold Rminus.
  
  assert (H1: a = d + (- (b + c))).
  {
    (* a + (b + c) = d means a = d - (b + c) *)
    apply Rplus_eq_reg_r with (r := b + c).
    rewrite Rplus_assoc.
    rewrite Rplus_opp_l.
    rewrite Rplus_0_r.
    exact H.
  }
  
  assert (H_distrib: -(b + c) = -b + -c).
  {
    apply Ropp_plus_distr.
  }
  
  rewrite H1.
  rewrite H_distrib.
  
  rewrite Rplus_assoc.
  
  reflexivity.
Qed.

Theorem algebraic_associativity : forall a b c d e f : R,
  a + b + c + d + e + f = a + (b + c + d + e) + f.
Proof.
  intros a b c d e f.
  
  rewrite <- Rplus_assoc.
  rewrite <- Rplus_assoc.
  rewrite <- Rplus_assoc.

  reflexivity.
Qed.

Theorem algebraic_cancel : forall α δ ρ γ : R,
δ + α + δ + α + ρ = δ + α + γ + δ + α + γ ->
    ρ = γ + γ.
Proof.
    intros α δ ρ γ.
    intros H.
    lra.
Qed.

(*  triangle C E A + angle A E D = angle D E B + angle A E D *)
Theorem algebraic_cancel2 : forall a b c : R,
a + b = c + b ->
    a = c.
Proof.
    intros a b c.
    intros H.
    lra.
Qed.

Theorem angle_cancel2 : forall A B C D E : Point,
    angle C E A + angle A E D = angle D E B + angle A E D ->
    angle C E A = angle D E B.
Proof.
    intros A B C D E.
    intros H.
    apply algebraic_cancel2 with
        (a := angle C E A)
        (b := angle A E D)
        (c := angle D E B).
    apply H.
Qed.
    

Theorem angle_sum_rearrangement : forall A B C D : Point,
  angle D B A + angle B D C + angle A D B + angle D B A + angle B D C + angle A D B = 
  angle D B A + (angle B D C + angle A D B + angle D B A + angle B D C) + angle A D B.
Proof.
  intros A B C D.
  
  apply algebraic_associativity with 
    (a := angle D B A)
    (b := angle B D C)
    (c := angle A D B)
    (d := angle D B A)
    (e := angle B D C)
    (f := angle A D B).
Qed.

Theorem angle_sum_application : forall A D C,
  angle A D C + angle D C A + angle C A D = 180 ->
  angle D C A = 180 - angle A D C - angle C A D.
Proof.
  intros A D C H.
  
  assert (H_assoc: angle A D C + (angle D C A + angle C A D) = 180).
  {
    rewrite <- Rplus_assoc.
    exact H.
  }
  
  assert (H_reorder: angle D C A + (angle A D C + angle C A D) = 180).
  {
    rewrite (Rplus_comm (angle A D C) (angle D C A + angle C A D)) in H_assoc.
    rewrite Rplus_assoc in H_assoc.
    rewrite (Rplus_comm (angle C A D) (angle A D C)) in H_assoc.
    exact H_assoc.
  }
  
  apply algebraic_rearrangement with (a := angle D C A) (b := angle A D C) 
                                    (c := angle C A D) (d := 180).
  exact H_reorder.
Qed.


Theorem angle_lemma_detailed_proof : forall A B C D : Point, forall α γ δ ρ : R,
  on_circle A -> on_circle B -> on_circle D ->
  C = center ->
  angle A D B = γ ->
  angle B D C = α ->
  angle D B A = δ ->
  angle A C B = ρ ->
  isosceles A D C ->
  isosceles B D C ->
  isosceles A B C ->
  triangle A D B ->
    ρ = 2 * γ.
Proof.
  intros A B C D α γ δ ρ HA HB HD HC HADB HBDC HDBA HACB2 Hiso_ADC Hiso_BDC Hiso_ABC Htri_ADB.
  
  (* Triangle ADC is isosceles, so angle DAC = γ + α *)
  assert (angle D A C = angle A D C) as HDAC_eq_DCA.
  { 
    (* Showing that two angles of the isosceles are same in ADC *)
    destruct Hiso_ADC as [_ Hiso].
    assert (angle A D C = angle C D A) as Hcomm.
    { 
        apply angle_comm.
    }
    rewrite <- Hcomm in Hiso.
    exact Hiso.
  }

  assert (angle C D B = angle C B D) as HCDB_eq_CBD.
  { 
    (* Showing that two angles of the isosceles are same in CDB *)
    destruct Hiso_BDC as [_ Hiso].
    assert (angle C B D = angle D B C) as Hcomm.
    { 
        apply angle_comm.
    }
    rewrite <- Hcomm in Hiso. symmetry.
    exact Hiso.
  }

  assert (angle C A B = angle C B A) as HCAB_eq_CBA.
  { 
    (* Showing that two angles of the isosceles are same in CBA *)
    destruct Hiso_ABC as [_ Hiso].
    assert (angle C A B = angle B A C) as Hcomm.
    { 
        apply angle_comm.
    }
    rewrite <- Hcomm in Hiso.
    exact Hiso.
  }
  
  (* From the above, we have angle DAC = γ + α *)
  assert (angle A D C = γ + α) as HADC.
  { assert (angle A D B + angle B D C = angle A D C) as Hadd.
    {
        apply angle_addition.
    }
    rewrite HADB in Hadd. rewrite HBDC in Hadd. symmetry. apply Hadd.
   }
   assert (angle D A C = angle A D C) as HDAC.
   {
    destruct Hiso_ADC.
    assert (angle A D C = angle C D A) as Hcomm.
    { 
        apply angle_comm.
    }
    rewrite <- Hcomm in H0.
    apply H0.
   }
  
  (* Using angle sum in triangle, angle DCA = 180 - 2(γ + α) *)
  assert (angle D C A = 180 - (γ + α) - (γ + α)) as HDCA.
  { 
    destruct Hiso_ADC.
    (*triangle A B C -> angle A B C + angle B C A + angle C A B*)
    assert (angle A D C + angle D C A + angle C A D = 180) as Hsum.
    {
        apply triangle_angle_sum. apply H.
    }
    rewrite <- HADC at 1.
    rewrite <- HDAC_eq_DCA in HADC.
    rewrite <- HADC.
    assert (Hdif: angle A D C + angle D C A + angle C A D - angle D C A = 180 - angle D C A).
    {
        rewrite Hsum. reflexivity.
    }
    assert (angle D A C = angle C A D) as Hcomm.
    { 
        apply angle_comm.
    }
    rewrite Hcomm.
    apply angle_sum_application.
    apply Hsum.
    }
  
  (* Triangle BDC is isosceles, so angle BDC = angle DBC = α *)
  assert (angle D B C = α) as HDBC.
  {
    destruct Hiso_BDC as [_ Hiso].
    assert (angle B D C = angle C D B) as Hcomm.
    { 
        apply angle_comm.
    }
    rewrite <- Hcomm in Hiso.
    rewrite Hiso. exact HBDC.
  }
  
  (* Triangle ABC is isosceles with angle ACB = δ + α *)
  assert (angle A B C = δ + α) as HACB.
  {
    assert (angle A B D = angle D B A) as Hcomm.
    { 
        apply angle_comm.
    }
    rewrite <- HDBA.
    rewrite <- HDBC.
    assert (angle A B D + angle D B C = angle A B C) as Hadd.
    {
        apply angle_addition.
    }
    rewrite <- Hcomm.
    symmetry.
    rewrite Hadd. reflexivity.
  }
  
  (* Summing angles in triangle ABC: 2(δ + α) + ρ = 180 *)
  assert ((δ + α) + (δ + α) + ρ = 180) as Hsum_ABC.
  { 
    rewrite <- HACB.
    assert (angle A B C = angle C B A) by apply angle_comm.
    rewrite H at 2.
    rewrite <- HACB2.
    destruct Hiso_ABC.
    rewrite <- H1.
    assert (angle B A C = angle C A B) by apply angle_comm.
    rewrite H2.
    assert (angle A C B = angle B C A) by apply angle_comm.
    rewrite Rplus_assoc.
    rewrite (Rplus_comm (angle C A B) (angle A C B)).
    rewrite <- Rplus_assoc.
    rewrite H3.

    (*triangle A B C -> angle A B C + angle B C A + angle C A B*)
    assert (angle A B C + angle B C A + angle C A B = 180) as Hsum.
    {
        apply triangle_angle_sum. apply H0.
    }
    exact Hsum.
  }
  
  (* For triangle ABD: 2(δ + α + γ) = 180 *)
  assert (δ + α + γ + δ + α + γ = 180) as Hsum_ABD.
  {
    rewrite <- HADB.
    rewrite <- HDBA.
    rewrite <- HBDC.
    assert ( angle B D C + angle A D B + angle D B A + angle B D C = angle D A B ).
    {
        rewrite <- Rplus_comm. rewrite <- Rplus_comm.
        assert ( angle D B A + angle B D C = angle C A B) as Hadd.
        {
            assert (angle B D C = angle C D B) as Hcomm.
            { 
                apply angle_comm.
            }
            rewrite Hcomm.
            assert (angle D B A = angle A B D) as Hcomm2.
            { 
                apply angle_comm.
            }
            rewrite Hcomm2.
            rewrite HCDB_eq_CBD.
            assert (angle C B D = angle D B C) as Hcomm3.
            { 
                apply angle_comm.
            }
            rewrite Hcomm3.
            rewrite HCAB_eq_CBA.
            assert (angle C B A = angle A B C) as Hcomm4.
            { 
                apply angle_comm.
            }
            rewrite Hcomm4.
            apply angle_addition.
        }
        rewrite Rplus_assoc.
        rewrite Hadd.
        assert ( angle B D C + angle A D B = angle D A C) as Hgettingthere.
        {
            rewrite Rplus_comm.
            rewrite HDAC_eq_DCA.
            apply angle_addition.
        }
        rewrite Rplus_comm.
        rewrite Hgettingthere.
        rewrite Rplus_comm.
        apply angle_addition.
    }
    rewrite angle_sum_rearrangement.
    rewrite H.
    (*triangle A B C -> angle A B C + angle B C A + angle C A B*)
    (* ADB -> ADB + DBA + BAD *)
    rewrite Rplus_comm.
    rewrite <- Rplus_assoc.
    assert (angle D A B = angle B A D) by apply angle_comm.
    rewrite H0.
    apply triangle_angle_sum.
    apply Htri_ADB.
  }
  
  (* Combining equations: 2(δ + α) + ρ = 2(δ + α + γ) *)
  assert ( δ + α + δ + α + ρ = δ + α + γ + δ + α + γ) as Hcombined.
  {
    rewrite <- Rplus_assoc in Hsum_ABC.
    rewrite Hsum_ABC. rewrite Hsum_ABD. reflexivity.
  }
  
  (* Simplifying to get ρ = 2γ *)
  assert (ρ =  γ + γ) as Hresult.
  {
    assert (δ + α + δ + α + ρ = δ + α + γ + δ + α + γ ->
    ρ = γ + γ).
    {
        intros H.
        lra.
    }
    apply H in Hcombined.
    apply Hcombined.
  }
  
  (* Conclude that angle ACB = 2γ *)
  - assert (ρ = γ + γ -> ρ = 2 * γ).
    { intros H.
        rewrite H.
        replace 2 with (1 + 1) by ring.
        rewrite Rmult_plus_distr_r.
        rewrite Rmult_1_l.
        reflexivity. }
    apply H in Hresult.
    apply Hresult.
Qed.

Definition line (A B : Point) :=
    A <> B.

Theorem vertical_angles_equal : 
  forall A B C D E : Point,
  line A B -> line C D -> 
  (* E is the intersection point *)
  E <> A -> E <> B -> E <> C -> E <> D ->
  angle C E A + angle A E D = 180 ->
  angle D E B + angle A E D = 180 ->
  angle D E B + angle C E B = 180 ->
  angle A E C + angle C E B = 180 ->
  angle C E A = angle D E B /\ angle A E D = angle B E C.
Proof.
  intros A B C D E.
  intros H_AB H_CD H_EA H_EB H_EC H_ED.
  intros H_supp1 H_supp2 H_supp3 H_supp4.
  
  assert (H_eq: angle C E A + angle A E D = angle D E B + angle A E D).
  { rewrite H_supp1. rewrite H_supp2. reflexivity. }
  
  assert (H_opp1: angle C E A = angle D E B).
  {
    apply angle_cancel2.
    apply H_eq.
  }
  
  assert (H_eq2: angle D E B + angle C E B = angle D E B + angle A E D).
  { rewrite H_supp3. rewrite H_supp2. reflexivity. }

  assert (H_opp2: angle C E B = angle A E D).
  {
    rewrite Rplus_comm in H_eq2.
    symmetry in H_eq2.
    rewrite Rplus_comm in H_eq2.
    apply algebraic_cancel2 with
        (a := angle C E B)
        (b := angle D E B)
        (c := angle A E D).
    symmetry.
    apply H_eq2.
  }
  
  split.
  - exact H_opp1.
  - assert (angle B E C = angle C E B) as Hcomm.
    { 
        apply angle_comm.
    }
    rewrite Hcomm.
    symmetry.
  exact H_opp2.
Qed.
    