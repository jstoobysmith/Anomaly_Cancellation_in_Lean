/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.SMRHN.Basic
universe v u

namespace SMRHN
open SMνCharges
open SMνACCs
open BigOperators

@[simps!]
def chargesMapOfSpeciesMap {n m : ℕ} (f : (SMνSpecies n).charges →ₗ[ℚ] (SMνSpecies m).charges) :
    (SMνCharges n).charges →ₗ[ℚ] (SMνCharges m).charges where
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

lemma chargesMapOfSpeciesMap_toSpecies {n m : ℕ}
    (f : (SMνSpecies n).charges →ₗ[ℚ] (SMνSpecies m).charges)
    (S : (SMνCharges n).charges) (j : Fin 6) :
    toSpecies j (chargesMapOfSpeciesMap f S) =  (LinearMap.comp f (toSpecies j)) S := by
  erw [toSMSpecies_toSpecies_inv]


@[simps!]
def speciesFamilyProj {m n : ℕ} (h : n ≤ m) :
    (SMνSpecies m).charges →ₗ[ℚ] (SMνSpecies n).charges where
  toFun S := S ∘ Fin.castLE h
  map_add' S T := by
    funext i
    simp
  map_smul' a S := by
    funext i
    simp
    rw [show Rat.cast a = a from rfl]
    simp

def familyProjection {m n : ℕ} (h : n ≤ m) : (SMνCharges m).charges →ₗ[ℚ] (SMνCharges n).charges :=
  chargesMapOfSpeciesMap (speciesFamilyProj h)

@[simps!]
def speciesEmbed (m n : ℕ) :
    (SMνSpecies m).charges →ₗ[ℚ] (SMνSpecies n).charges where
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

def familyEmbedding (m n : ℕ) : (SMνCharges m).charges →ₗ[ℚ] (SMνCharges n).charges :=
  chargesMapOfSpeciesMap (speciesEmbed m n)

@[simps!]
def speciesFamilyUniversial (n : ℕ) :
    (SMνSpecies 1).charges →ₗ[ℚ] (SMνSpecies n).charges where
  toFun S _ := S 0
  map_add' S T := by
    funext _
    simp
  map_smul' a S := by
    funext i
    simp
    rw [show Rat.cast a = a from rfl]
    simp

def familyUniversal (n : ℕ) : (SMνCharges 1).charges →ₗ[ℚ] (SMνCharges n).charges :=
  chargesMapOfSpeciesMap (speciesFamilyUniversial n)


@[simp]
lemma toSpecies_familyUniversal {n : ℕ} (j : Fin 6) (S : (SMνCharges 1).charges)
    (i : Fin n) : toSpecies j (familyUniversal n S) i = toSpecies j S 0 := by
  erw [chargesMapOfSpeciesMap_toSpecies]
  rfl

lemma sum_familyUniversal {n : ℕ} (m : ℕ) (S : (SMνCharges 1).charges) (j : Fin 6) :
    ∑ i, ((fun a => a ^ m) ∘ toSpecies j (familyUniversal n S)) i =
    n * (toSpecies j S 0) ^ m := by
  simp
  have h1 : (n : ℚ) * (toSpecies j S 0) ^ m = ∑ _i : Fin n,  (toSpecies j S 0) ^ m:= by
    rw [Fin.sum_const]
    simp
  erw [h1]
  apply Finset.sum_congr
  simp
  intro i _
  erw [toSpecies_familyUniversal]

lemma sum_familyUniversal_one  {n : ℕ} (S : (SMνCharges 1).charges) (j : Fin 6) :
    ∑ i, toSpecies j (familyUniversal n S) i = n * (toSpecies j S 0) := by
  simpa using sum_familyUniversal 1 S j

lemma sum_familyUniversal_two {n : ℕ} (S : (SMνCharges 1).charges)
    (T : (SMνCharges n).charges) (j : Fin 6) :
    ∑ i, (toSpecies j (familyUniversal n S) i * toSpecies j T i) =
    (toSpecies j S 0) * ∑ i, toSpecies j T i := by
  simp
  rw [Finset.mul_sum]
  apply Finset.sum_congr
  simp
  intro i _
  erw [toSpecies_familyUniversal]
  rfl

lemma sum_familyUniversal_three  {n : ℕ} (S : (SMνCharges 1).charges)
    (T L : (SMνCharges n).charges) (j : Fin 6) :
    ∑ i, (toSpecies j (familyUniversal n S) i * toSpecies j T i * toSpecies j L i) =
    (toSpecies j S 0) * ∑ i, toSpecies j T i * toSpecies j L i := by
  simp
  rw [Finset.mul_sum]
  apply Finset.sum_congr
  simp
  intro i _
  erw [toSpecies_familyUniversal]
  simp
  ring

lemma familyUniversal_accGrav (S : (SMνCharges 1).charges) :
    accGrav (familyUniversal n S)  = n * (accGrav S) := by
  rw [accGrav_decomp, accGrav_decomp]
  repeat rw [sum_familyUniversal_one]
  simp
  ring

lemma familyUniversal_accSU2 (S : (SMνCharges 1).charges) :
    accSU2 (familyUniversal n S)  = n * (accSU2 S) := by
  rw [accSU2_decomp, accSU2_decomp]
  repeat rw [sum_familyUniversal_one]
  simp
  ring

lemma familyUniversal_accSU3 (S : (SMνCharges 1).charges) :
    accSU3 (familyUniversal n S)  = n * (accSU3 S) := by
  rw [accSU3_decomp, accSU3_decomp]
  repeat rw [sum_familyUniversal_one]
  simp
  ring

lemma familyUniversal_accYY (S : (SMνCharges 1).charges) :
    accYY (familyUniversal n S)  = n * (accYY S) := by
  rw [accYY_decomp, accYY_decomp]
  repeat rw [sum_familyUniversal_one]
  simp
  ring

lemma familyUniversal_quadBiLin (S : (SMνCharges 1).charges) (T : (SMνCharges n).charges) :
    quadBiLin (familyUniversal n S, T) =
    S 0 * ∑ i, Q T i - 2 * S 1 * ∑ i, U T i + S 2 *∑ i, D T i -
    S 3 * ∑ i, L T i + S 4 * ∑ i, E T i  := by
  rw [quadBiLin_decomp]
  repeat rw [sum_familyUniversal_two]
  repeat rw [toSpecies_one]
  simp
  ring

lemma familyUniversal_accQuad (S : (SMνCharges 1).charges) :
    accQuad (familyUniversal n S)  = n * (accQuad S) := by
  rw [accQuad_decomp]
  repeat erw [sum_familyUniversal]
  rw [accQuad_decomp]
  simp
  ring

lemma familyUniversal_cubeTriLin (S : (SMνCharges 1).charges) (T R : (SMνCharges n).charges) :
    cubeTriLin (familyUniversal n S, T, R) = 6 * S 0 * ∑ i, (Q T i * Q R i) +
      3 * S 1 * ∑ i,  (U T i * U R i) + 3 * S 2 * ∑ i,  (D T i * D R i)
      + 2 * S 3 * ∑ i, (L T i * L R i) +
      S 4 * ∑ i, (E T i * E R i) + S 5 * ∑ i, (N T i * N R i) := by
  rw [cubeTriLin_decomp]
  repeat rw [sum_familyUniversal_three]
  repeat rw [toSpecies_one]
  simp
  ring

lemma familyUniversal_cubeTriLin' (S T : (SMνCharges 1).charges) (R : (SMνCharges n).charges) :
    cubeTriLin (familyUniversal n S, familyUniversal n T, R) =
      6 * S 0 * T 0 * ∑ i, Q R i + 3 * S 1 * T 1 * ∑ i, U R i
      + 3 * S 2 * T 2 * ∑ i, D R i + 2 * S 3 * T 3 * ∑ i, L R i +
      S 4 * T 4 * ∑ i, E R i + S 5 * T 5 * ∑ i, N R i := by
  rw [familyUniversal_cubeTriLin]
  repeat rw [sum_familyUniversal_two]
  repeat rw [toSpecies_one]
  simp
  ring

lemma familyUniversal_accCube (S : (SMνCharges 1).charges) :
    accCube (familyUniversal n S) = n * (accCube S) := by
  rw [accCube_decomp]
  repeat erw [sum_familyUniversal]
  rw [accCube_decomp]
  simp
  ring

end SMRHN
