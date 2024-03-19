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
def SMRHNPlusU1SpeciesMap (m n : ℕ) :
    (SMRHNPlusU1Species m).charges →ₗ[ℚ] (SMRHNPlusU1Species n).charges where
  toFun S := fun i =>
    if hi : i.val < m then
      S ⟨i, hi⟩
    else
      0
  map_add' S T := by
    funext i
    simp
    by_cases hi : i.val < m
    erw [dif_pos hi, dif_pos hi, dif_pos hi]
    erw [dif_neg hi, dif_neg hi, dif_neg hi]
    rfl
  map_smul' a S := by
    funext i
    simp
    by_cases hi : i.val < m
    erw [dif_pos hi, dif_pos hi]
    rfl
    erw [dif_neg hi, dif_neg hi]
    simp

def SMRHNPlusU1Map (m n : ℕ) : (SMRHNPlusU1 m).charges →ₗ[ℚ] (SMRHNPlusU1 n).charges where
  toFun S := mkFromSpecies
      ((LinearMap.comp (SMRHNPlusU1SpeciesMap m n) Q ) S)
      ((LinearMap.comp (SMRHNPlusU1SpeciesMap m n) U ) S)
      ((LinearMap.comp (SMRHNPlusU1SpeciesMap m n) D ) S)
      ((LinearMap.comp (SMRHNPlusU1SpeciesMap m n) L ) S)
      ((LinearMap.comp (SMRHNPlusU1SpeciesMap m n) E ) S)
      ((LinearMap.comp (SMRHNPlusU1SpeciesMap m n) N ) S)
  map_add' S T := by
    apply SMRHNPlusU1Charges.ext
    rw [Q.map_add', mkFromSpecies_Q, mkFromSpecies_Q, mkFromSpecies_Q,
      (SMRHNPlusU1SpeciesMap m n ∘ₗ Q).map_add]
    rw [U.map_add', mkFromSpecies_U, mkFromSpecies_U, mkFromSpecies_U,
      (SMRHNPlusU1SpeciesMap m n ∘ₗ U).map_add]
    rw [D.map_add', mkFromSpecies_D, mkFromSpecies_D, mkFromSpecies_D,
      (SMRHNPlusU1SpeciesMap m n ∘ₗ D).map_add]
    rw [L.map_add', mkFromSpecies_L, mkFromSpecies_L, mkFromSpecies_L,
      (SMRHNPlusU1SpeciesMap m n ∘ₗ L).map_add]
    rw [E.map_add', mkFromSpecies_E, mkFromSpecies_E, mkFromSpecies_E,
      (SMRHNPlusU1SpeciesMap m n ∘ₗ E).map_add]
    rw [N.map_add', mkFromSpecies_N, mkFromSpecies_N, mkFromSpecies_N,
      (SMRHNPlusU1SpeciesMap m n ∘ₗ N).map_add]
  map_smul' a S := by
    apply SMRHNPlusU1Charges.ext
    rw [Q.map_smul', mkFromSpecies_Q, mkFromSpecies_Q, (SMRHNPlusU1SpeciesMap m n ∘ₗ Q).map_smul]
    rfl
    rw [U.map_smul', mkFromSpecies_U, mkFromSpecies_U, (SMRHNPlusU1SpeciesMap m n ∘ₗ U).map_smul]
    rfl
    rw [D.map_smul', mkFromSpecies_D, mkFromSpecies_D, (SMRHNPlusU1SpeciesMap m n ∘ₗ D).map_smul]
    rfl
    rw [L.map_smul', mkFromSpecies_L, mkFromSpecies_L, (SMRHNPlusU1SpeciesMap m n ∘ₗ L).map_smul]
    rfl
    rw [E.map_smul', mkFromSpecies_E, mkFromSpecies_E, (SMRHNPlusU1SpeciesMap m n ∘ₗ E).map_smul]
    rfl
    rw [N.map_smul', mkFromSpecies_N, mkFromSpecies_N, (SMRHNPlusU1SpeciesMap m n ∘ₗ N).map_smul]
    rfl



end SMRHNPlusU1
