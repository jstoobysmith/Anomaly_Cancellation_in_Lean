/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.SMRHNPlusU1.Basic
import AnomalyCancellationInLean.SMRHNPlusU1.FamilyUniversal
import AnomalyCancellationInLean.SMRHNPlusU1.OneFamily.BMinusL
import Mathlib.Tactic.Polyrith
import AnomalyCancellationInLean.GroupActions

universe v u

namespace SMRHNPlusU1
open SMRHNPlusU1Charges
open SMRHNPlusU1ACCs
open BigOperators

@[simps!]
def BMinusLNFamily (n : ℕ) : (SMRHNPlusU1 n).AnomalyFree :=
  (familyUniversalHom n).anomalyFree BMinusLOneFamily

lemma accQuadBiLinear_BMinusL {n : ℕ} (S : (SMRHNPlusU1 n).charges) :
    accQuadBiLinear.toFun ((BMinusLNFamily n).val, S) =
     1/2 * accYY S + 3/2 * accSU2 S  + (- 2 * accSU3 S) := by
  rw [accQuadBiLinear, accYY, accSU2, accSU3]
  simp only [SMRHNPlusU1Charges_charges, SMRHNPlusU1Species_charges, BMinusLNFamily_val,
   LinearMap.coe_toAddHom, neg_mul, one_div, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib,
   ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Fintype.sum_congr
  intro i
  erw [mkFromSpecies_Q, mkFromSpecies_U, mkFromSpecies_D, mkFromSpecies_L, mkFromSpecies_E]
  simp
  ring

lemma accCubeTriLinear_BMinusL₂ {n : ℕ} (S : (SMRHNPlusU1 n).charges) :
    accCubeTriLinSymm.toFun ((BMinusLNFamily n).val, (BMinusLNFamily n).val, S) =
    9 * accGrav S  + (- 24 * accSU3 S) := by
  rw [accCubeTriLinSymm, accGrav, accSU3]
  simp only [SMRHNPlusU1Charges_charges, SMRHNPlusU1Species_charges, BMinusLNFamily_val,
   LinearMap.coe_toAddHom, neg_mul, one_div, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib,
   ← Finset.sum_add_distrib]
  rw [accCubeTriLinToFun]
  apply Fintype.sum_congr
  intro i
  erw [mkFromSpecies_Q, mkFromSpecies_U, mkFromSpecies_D, mkFromSpecies_L, mkFromSpecies_E,
   mkFromSpecies_N]
  simp
  ring

lemma accCubeTriLinear_BMinusL₂_AnomalyFreeLinear {n : ℕ} (S : (SMRHNPlusU1 n).AnomalyFreeLinear) :
    accCubeTriLinSymm.toFun ((BMinusLNFamily n).val, (BMinusLNFamily n).val, S.val) = 0 := by
  rw [accCubeTriLinear_BMinusL₂]
  have h := S.linearSol
  simp at h
  erw [h 0, h 2]
  simp


def anomalyFreeQuadPlusBMinusL (a : ℚ) (S : (SMRHNPlusU1 n).AnomalyFreeQuad) :
    (SMRHNPlusU1 n).AnomalyFreeQuad :=
  ⟨S.1 + a • (BMinusLNFamily n).1.1, by
    intro i
    simp at i
    match i with
    | 0 =>
      erw [BiLinearSymm.toHomogeneousQuad_add]
      have hS := S.quadSol
      simp at hS
      have hS' := S.linearSol
      simp at hS'
      have hBL := (BMinusLNFamily n).quadSol
      simp at hBL
      erw [hS 0]
      erw [accQuadBiLinear.map_smul₂]
      rw [accQuadBiLinear.swap, accQuadBiLinear_BMinusL]
      erw [hS' 1, hS' 2, hS' 3]
      simp only [zero_add, one_div, mul_zero, add_zero]
      change accQuad.toFun (a • _) = _
      rw [accQuad.map_smul']
      erw [hBL 0]
      simp⟩

lemma anomalyFreeQuadPlusBMinusL_zero  (S : (SMRHNPlusU1 n).AnomalyFreeQuad) :
    anomalyFreeQuadPlusBMinusL 0 S = S := by
  simp [anomalyFreeQuadPlusBMinusL]

end SMRHNPlusU1
