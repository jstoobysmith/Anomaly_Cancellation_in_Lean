/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.SM.Basic
universe v u

namespace SM
open SMCharges
open SMACCs
open BigOperators

@[simps!]
def chargesMapOfSpeciesMap {n m : ℕ} (f : (SMSpecies n).charges →ₗ[ℚ] (SMSpecies m).charges) :
    (SMCharges n).charges →ₗ[ℚ] (SMCharges m).charges where
  toFun S := toSpeciesEquiv.symm (fun i => (LinearMap.comp f (toSpecies i)) S)
  map_add' S T := by
    rw [charges_eq_toSpecies_eq]
    intro i
    rw [map_add]
    rw [toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv]
    rw [map_add]
  map_smul' a S := by
    rw [charges_eq_toSpecies_eq]
    intro i
    rw [map_smul]
    rw [toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv]
    rw [map_smul]
    rfl

@[simps!]
def speciesFamilyProj {m n : ℕ} (h : n ≤ m) :
    (SMSpecies m).charges →ₗ[ℚ] (SMSpecies n).charges where
  toFun S := S ∘ Fin.castLE h
  map_add' S T := by
    funext i
    simp
  map_smul' a S := by
    funext i
    simp
    rw [show Rat.cast a = a from rfl]
    simp

def familyProjection {m n : ℕ} (h : n ≤ m) : (SMCharges m).charges →ₗ[ℚ] (SMCharges n).charges :=
  chargesMapOfSpeciesMap (speciesFamilyProj h)

@[simps!]
def speciesEmbed (m n : ℕ) :
    (SMSpecies m).charges →ₗ[ℚ] (SMSpecies n).charges where
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

def familyEmbedding (m n : ℕ) : (SMCharges m).charges →ₗ[ℚ] (SMCharges n).charges :=
  chargesMapOfSpeciesMap (speciesEmbed m n)

@[simps!]
def speciesFamilyUniversial (n : ℕ) :
    (SMSpecies 1).charges →ₗ[ℚ] (SMSpecies n).charges where
  toFun S _ := S 0
  map_add' S T := by
    funext _
    simp
  map_smul' a S := by
    funext i
    simp
    rw [show Rat.cast a = a from rfl]
    simp

def familyUniversal ( n : ℕ) : (SMCharges 1).charges →ₗ[ℚ] (SMCharges n).charges :=
  chargesMapOfSpeciesMap (speciesFamilyUniversial n)

end SM
