/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.SMRHNPlusU1.Basic
import Mathlib.Tactic.Polyrith
import AnomalyCancellationInLean.GroupActions
universe v u

namespace SMRHNPlusU1
open SMRHNPlusU1Charges
open SMRHNPlusU1ACCs
open BigOperators

@[simps!]
def familyUniversalCharges (n : ℕ) : (SMRHNPlusU1 1).charges →ₗ[ℚ] (SMRHNPlusU1 n).charges where
  toFun S := mkFromSpecies (fun _ => S 0) (fun _ => S 1) (fun _ => S 2)
    (fun _ => S 3) (fun _ => S 4) (fun _ => S 5)
  map_add' S T := by
    apply SMRHNPlusU1Charges.ext
    rw [mkFromSpecies_Q, Q.map_add', mkFromSpecies_Q, mkFromSpecies_Q]
    rfl
    rw [mkFromSpecies_U, U.map_add', mkFromSpecies_U, mkFromSpecies_U]
    rfl
    rw [mkFromSpecies_D, D.map_add', mkFromSpecies_D, mkFromSpecies_D]
    rfl
    rw [mkFromSpecies_L, L.map_add', mkFromSpecies_L, mkFromSpecies_L]
    rfl
    rw [mkFromSpecies_E, E.map_add', mkFromSpecies_E, mkFromSpecies_E]
    rfl
    rw [mkFromSpecies_N, N.map_add', mkFromSpecies_N, mkFromSpecies_N]
    rfl
  map_smul' a S := by
    apply SMRHNPlusU1Charges.ext
    rw [mkFromSpecies_Q, Q.map_smul', mkFromSpecies_Q]
    rfl
    rw [mkFromSpecies_U, U.map_smul', mkFromSpecies_U]
    rfl
    rw [mkFromSpecies_D, D.map_smul', mkFromSpecies_D]
    rfl
    rw [mkFromSpecies_L, L.map_smul', mkFromSpecies_L]
    rfl
    rw [mkFromSpecies_E, E.map_smul', mkFromSpecies_E]
    rfl
    rw [mkFromSpecies_N, N.map_smul', mkFromSpecies_N]
    rfl

lemma familyUniversalCharges_Grav {n : ℕ} (S : (SMRHNPlusU1 1).AnomalyFree) :
    accGrav (familyUniversalCharges n S.val) = 0 := by
  simp only [SMRHNPlusU1Charges_charges, accGrav, SMRHNPlusU1Species_charges, SMRHNPlusU1_charges,
    LinearMap.coe_mk, AddHom.coe_mk]
  apply Fintype.sum_eq_zero
  intro i
  erw [mkFromSpecies_Q, mkFromSpecies_U, mkFromSpecies_D, mkFromSpecies_L, mkFromSpecies_E,
   mkFromSpecies_N]
  let h := S.linearSol
  simp at h
  exact h 0

lemma familyUniversalCharges_SU2 {n : ℕ} (S : (SMRHNPlusU1 1).AnomalyFree) :
    accSU2 (familyUniversalCharges n S.val) = 0 := by
  simp only [SMRHNPlusU1Charges_charges, accSU2, SMRHNPlusU1Species_charges, SMRHNPlusU1_charges,
    LinearMap.coe_mk, AddHom.coe_mk]
  apply Fintype.sum_eq_zero
  intro i
  erw [mkFromSpecies_Q, mkFromSpecies_L]
  let h := S.linearSol
  simp at h
  exact h 1

lemma familyUniversalCharges_SU3 {n : ℕ} (S : (SMRHNPlusU1 1).AnomalyFree) :
    accSU3 (familyUniversalCharges n S.val) = 0 := by
  simp only [SMRHNPlusU1Charges_charges, accSU3, SMRHNPlusU1Species_charges, SMRHNPlusU1_charges,
    LinearMap.coe_mk, AddHom.coe_mk]
  apply Fintype.sum_eq_zero
  intro i
  erw [mkFromSpecies_Q, mkFromSpecies_U, mkFromSpecies_D]
  let h := S.linearSol
  simp at h
  exact h 2

lemma familyUniversalCharges_YY {n : ℕ} (S : (SMRHNPlusU1 1).AnomalyFree) :
    accYY (familyUniversalCharges n S.val) = 0 := by
  simp only [SMRHNPlusU1Charges_charges, accYY, SMRHNPlusU1Species_charges, SMRHNPlusU1_charges,
    LinearMap.coe_mk, AddHom.coe_mk]
  apply Fintype.sum_eq_zero
  intro i
  erw [mkFromSpecies_Q, mkFromSpecies_U, mkFromSpecies_D, mkFromSpecies_L, mkFromSpecies_E]
  let h := S.linearSol
  simp at h
  exact h 3

lemma familyUniversalCharges_Quad {n : ℕ} (S : (SMRHNPlusU1 1).AnomalyFree) :
    accQuad.toFun (familyUniversalCharges n S.val) = 0 := by
  simp only [SMRHNPlusU1Charges_charges, accQuad, SMRHNPlusU1Species_charges, SMRHNPlusU1_charges,
    LinearMap.coe_mk, AddHom.coe_mk]
  apply Fintype.sum_eq_zero
  intro i
  erw [mkFromSpecies_Q, mkFromSpecies_U, mkFromSpecies_D, mkFromSpecies_L, mkFromSpecies_E]
  let h := S.quadSol
  simp at h
  have h0 := h 0
  simpa using h0

lemma familyUniversalCharges_Cubic {n : ℕ} (S : (SMRHNPlusU1 1).AnomalyFree) :
    accCube.toFun (familyUniversalCharges n S.val) = 0 := by
  simp only [SMRHNPlusU1Charges_charges, accCube, SMRHNPlusU1Species_charges, SMRHNPlusU1_charges,
    LinearMap.coe_mk, AddHom.coe_mk]
  apply Fintype.sum_eq_zero
  intro i
  erw [mkFromSpecies_Q, mkFromSpecies_U, mkFromSpecies_D, mkFromSpecies_L, mkFromSpecies_E,
  mkFromSpecies_N]
  let h := S.cubicSol
  simpa using h

def familyUniversalAnomalyFree (n : ℕ) (S : (SMRHNPlusU1 1).AnomalyFree) :
    (SMRHNPlusU1 n).AnomalyFree where
  val := familyUniversalCharges n S.val
  linearSol := by
    intro i
    simp at i
    match i with
    | 0 => exact familyUniversalCharges_Grav S
    | 1 => exact familyUniversalCharges_SU2 S
    | 2 => exact familyUniversalCharges_SU3 S
    | 3 => exact familyUniversalCharges_YY S
  quadSol := by
    intro i
    simp at i
    match i with
    | 0 => exact familyUniversalCharges_Quad S
  cubicSol := familyUniversalCharges_Cubic S

def familyUniversalHom (n : ℕ) : ACCSystem.Hom  (SMRHNPlusU1 1)  (SMRHNPlusU1 n) where
  charges := familyUniversalCharges n
  anomalyFree := familyUniversalAnomalyFree n
  commute := rfl


end SMRHNPlusU1
