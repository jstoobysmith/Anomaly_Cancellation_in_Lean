/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.SMRHNPlusU1.Basic
import AnomalyCancellationInLean.SMRHNPlusU1.FamilyUniversal
import AnomalyCancellationInLean.SMRHNPlusU1.OneFamily.HyperCharge
import Mathlib.Tactic.Polyrith
import AnomalyCancellationInLean.GroupActions

universe v u

namespace SMRHNPlusU1
open SMRHNPlusU1Charges
open SMRHNPlusU1ACCs
open BigOperators

@[simps!]
def hyperChargeNFamily (n : ℕ) : (SMRHNPlusU1 n).AnomalyFree :=
  (familyUniversalHom n).anomalyFree hyperChargeOneFamily

lemma accQuadBiLinear_hyperCharge {n : ℕ} (S : (SMRHNPlusU1 n).charges) :
    accQuadBiLinear.toFun ((hyperChargeNFamily n).val, S) = accYY S := by
  rw [accQuadBiLinear, accYY]
  simp only
  apply Fintype.sum_congr
  intro i
  erw [mkFromSpecies_Q, mkFromSpecies_U, mkFromSpecies_D, mkFromSpecies_L, mkFromSpecies_E]
  simp
  ring

lemma accCubeTriLinear_hyperCharge₁ {n : ℕ} (S : (SMRHNPlusU1 n).charges) :
    accCubeTriLinSymm.toFun ((hyperChargeNFamily n).val, S, S) = 6 * accQuad.toFun S := by
  rw [accCubeTriLinSymm, accQuad, BiLinearSymm.toHomogeneousQuad, accQuadBiLinear]
  simp only
  rw [accCubeTriLinToFun, Finset.mul_sum]
  apply Fintype.sum_congr
  intro i
  erw [mkFromSpecies_Q, mkFromSpecies_U, mkFromSpecies_D, mkFromSpecies_L, mkFromSpecies_E, 
   mkFromSpecies_N]
  simp
  ring


lemma accCubeTriLinear_hyperCharge₂ {n : ℕ} (S : (SMRHNPlusU1 n).charges) :
    accCubeTriLinSymm.toFun ((hyperChargeNFamily n).val, (hyperChargeNFamily n).val, S) = 
    6 * accYY S := by
  rw [accCubeTriLinSymm, accYY]
  simp only
  simp only [accCubeTriLinToFun, SMRHNPlusU1Charges_charges, SMRHNPlusU1Species_charges,
    hyperChargeNFamily_val,  LinearMap.coe_toAddHom, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro i
  erw [mkFromSpecies_Q, mkFromSpecies_U, mkFromSpecies_D, mkFromSpecies_L, mkFromSpecies_E, 
   mkFromSpecies_N]
  simp
  ring



end SMRHNPlusU1
