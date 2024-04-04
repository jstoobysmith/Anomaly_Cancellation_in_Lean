/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import AnomalyCancellationInLean.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin
/-!
# Anomaly cancellation conditions for n family SM.
-/


universe v u
open Nat
open BigOperators

/-- Aassociate to each (including RHN) SM fermion a set of charges-/
@[simps!]
def SMνCharges (n : ℕ) : ACCSystemCharges := ACCSystemChargesMk (6 * n)

@[simps!]
def SMνSpecies (n : ℕ) : ACCSystemCharges := ACCSystemChargesMk n

namespace SMνCharges

variable  {n : ℕ}

@[simps!]
def toSpeciesEquiv : (SMνCharges n).charges ≃ (Fin 6 → Fin n → ℚ) :=
  ((Equiv.curry _ _ _).symm.trans ((@finProdFinEquiv 6 n).arrowCongr (Equiv.refl ℚ))).symm

@[simps!]
def toSpecies (i : Fin 6) : (SMνCharges n).charges →ₗ[ℚ] (SMνSpecies n).charges where
  toFun S := toSpeciesEquiv S i
  map_add' _ _ := by aesop
  map_smul' _ _ := by aesop

lemma charges_eq_toSpecies_eq (S T : (SMνCharges n).charges) :
    S = T ↔ ∀ i, toSpecies i S = toSpecies i T := by
  apply Iff.intro
  intro h
  rw [h]
  simp
  intro h
  apply toSpeciesEquiv.injective
  funext i
  exact h i

lemma toSMSpecies_toSpecies_inv (i : Fin 6) (f :  (Fin 6 → Fin n → ℚ) ) :
    (toSpecies i) (toSpeciesEquiv.symm f) = f i := by
  change (toSpeciesEquiv ∘ toSpeciesEquiv.symm ) _ i = f i
  simp

lemma toSpecies_one  (S : (SMνCharges 1).charges) (j : Fin 6) :
    toSpecies j S ⟨0, by simp⟩ = S j := by
  match j with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl
  | 5 => rfl

abbrev Q := @toSpecies n 0
abbrev U := @toSpecies n 1
abbrev D := @toSpecies n 2
abbrev L := @toSpecies n 3
abbrev E := @toSpecies n 4
abbrev N := @toSpecies n 5


end SMνCharges

namespace SMνACCs

open SMνCharges

variable  {n : ℕ}

/-- The gravitational anomaly equation. -/
@[simp]
def accGrav : (SMνCharges n).charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (6 * Q S i + 3 * U S i + 3 * D S i + 2 * L S i + E S i + N S i)
  map_add' S T := by
    simp only
    repeat rw [map_add]
    simp  [Pi.add_apply, mul_add]
    repeat erw [Finset.sum_add_distrib]
    ring
  map_smul' a S := by
    simp only
    repeat erw [map_smul]
    simp [HSMul.hSMul, SMul.smul]
    repeat erw [Finset.sum_add_distrib]
    repeat erw [← Finset.mul_sum]
    rw [show Rat.cast a = a from rfl]
    ring


lemma accGrav_decomp (S : (SMνCharges n).charges) :
    accGrav S = 6 * ∑ i, Q S i + 3 * ∑ i, U S i + 3 * ∑ i, D S i + 2 * ∑ i, L S i + ∑ i, E S i +
      ∑ i, N S i := by
  simp
  repeat erw [Finset.sum_add_distrib]
  repeat erw [← Finset.mul_sum]

/-- Extensionality lemma for `accGrav`. -/
lemma accGrav_ext {S T : (SMνCharges n).charges}
    (hj : ∀ (j : Fin 6),  ∑ i, (toSpecies j) S i = ∑ i, (toSpecies j) T i) :
    accGrav S = accGrav T := by
  rw [accGrav_decomp, accGrav_decomp]
  repeat erw [hj]


/-- The `SU(2)` anomaly equation. -/
@[simp]
def accSU2 : (SMνCharges n).charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (3 * Q S i + L S i)
  map_add' S T := by
    simp only
    repeat rw [map_add]
    simp  [Pi.add_apply, mul_add]
    repeat erw [Finset.sum_add_distrib]
    ring
  map_smul' a S := by
    simp only
    repeat erw [map_smul]
    simp [HSMul.hSMul, SMul.smul]
    repeat erw [Finset.sum_add_distrib]
    repeat erw [← Finset.mul_sum]
    rw [show Rat.cast a = a from rfl]
    ring

lemma accSU2_decomp (S : (SMνCharges n).charges) :
    accSU2 S = 3 * ∑ i, Q S i + ∑ i, L S i := by
  simp
  repeat erw [Finset.sum_add_distrib]
  repeat erw [← Finset.mul_sum]

/-- Extensionality lemma for `accSU2`. -/
lemma accSU2_ext {S T : (SMνCharges n).charges}
    (hj : ∀ (j : Fin 6),  ∑ i, (toSpecies j) S i = ∑ i, (toSpecies j) T i) :
    accSU2 S = accSU2 T := by
  rw [accSU2_decomp, accSU2_decomp]
  repeat erw [hj]

/-- The `SU(3)` anomaly equations. -/
@[simp]
def accSU3 : (SMνCharges n).charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (2 * Q S i + U S i + D S i)
  map_add' S T := by
    simp only
    repeat rw [map_add]
    simp  [ Pi.add_apply, mul_add]
    repeat erw [Finset.sum_add_distrib]
    ring
  map_smul' a S := by
    simp only
    repeat erw [map_smul]
    simp [HSMul.hSMul, SMul.smul]
    repeat erw [Finset.sum_add_distrib]
    repeat erw [← Finset.mul_sum]
    rw [show Rat.cast a = a from rfl]
    ring

lemma accSU3_decomp (S : (SMνCharges n).charges) :
    accSU3 S = 2 * ∑ i, Q S i + ∑ i, U S i + ∑ i, D S i := by
  simp
  repeat rw [Finset.sum_add_distrib]
  repeat rw [← Finset.mul_sum]

/-- Extensionality lemma for `accSU3`. -/
lemma accSU3_ext {S T : (SMνCharges n).charges}
    (hj : ∀ (j : Fin 6),  ∑ i, (toSpecies j) S i = ∑ i, (toSpecies j) T i) :
    accSU3 S = accSU3 T := by
  rw [accSU3_decomp, accSU3_decomp]
  repeat rw [hj]

/-- The `Y²` anomaly equation. -/
@[simp]
def accYY : (SMνCharges n).charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (Q S i + 8 * U S i + 2 * D S i + 3 * L S i
    + 6 * E S i)
  map_add' S T := by
    simp only
    repeat rw [map_add]
    simp  [Pi.add_apply, mul_add]
    repeat erw [Finset.sum_add_distrib]
    ring
  map_smul' a S := by
    simp only
    repeat erw [map_smul]
    simp [HSMul.hSMul, SMul.smul]
    repeat erw [Finset.sum_add_distrib]
    repeat erw [← Finset.mul_sum]
    rw [show Rat.cast a = a from rfl]
    ring

lemma accYY_decomp (S : (SMνCharges n).charges) :
    accYY S = ∑ i, Q S i + 8 * ∑ i, U S i + 2 * ∑ i, D S i + 3 * ∑ i, L S i + 6 * ∑ i, E S i := by
  simp
  repeat rw [Finset.sum_add_distrib]
  repeat rw [← Finset.mul_sum]

/-- Extensionality lemma for `accYY`. -/
lemma accYY_ext {S T : (SMνCharges n).charges}
    (hj : ∀ (j : Fin 6),  ∑ i, (toSpecies j) S i = ∑ i, (toSpecies j) T i) :
    accYY S = accYY T := by
  rw [accYY_decomp, accYY_decomp]
  repeat rw [hj]

/-- The quadratic bilinear map. -/
@[simps!]
def quadBiLin : BiLinearSymm (SMνCharges n).charges where
  toFun S := ∑ i, (Q S.1 i * Q S.2 i +
    - 2 * (U S.1 i * U S.2 i) +
    D S.1 i * D S.2 i +
    (- 1) * (L S.1 i * L S.2 i) +
    E S.1 i * E S.2 i)
  map_smul₁' a S T := by
    simp only
    rw [Finset.mul_sum]
    apply Fintype.sum_congr
    intro i
    repeat erw [map_smul]
    simp [HSMul.hSMul, SMul.smul]
    ring
  map_add₁' S T R := by
    simp only
    rw [← Finset.sum_add_distrib]
    apply Fintype.sum_congr
    intro i
    repeat erw [map_add]
    simp
    ring
  swap' S T := by
    simp
    apply Fintype.sum_congr
    intro i
    ring

lemma quadBiLin_decomp (S T : (SMνCharges n).charges) :
    quadBiLin (S, T) = ∑ i, Q S i * Q T i  - 2 *  ∑ i, U S i * U T i +
       ∑ i, D S i * D T i -  ∑ i, L S i * L T i +  ∑ i, E S i * E T i := by
  erw [← quadBiLin.toFun_eq_coe]
  rw [quadBiLin]
  simp only
  repeat erw [Finset.sum_add_distrib]
  repeat erw [← Finset.mul_sum]
  simp
  ring

/-- The quadratic anomaly cancellation condition. -/
@[simp]
def accQuad  : HomogeneousQuadratic (SMνCharges n).charges :=
  (@quadBiLin n).toHomogeneousQuad

lemma accQuad_decomp (S : (SMνCharges n).charges) :
    accQuad S = ∑ i, (Q S i)^2 - 2 * ∑ i, (U S i)^2 + ∑ i, (D S i)^2 - ∑ i, (L S i)^2
    + ∑ i, (E S i)^2 := by
  erw [quadBiLin_decomp]
  ring_nf

/-- Extensionality lemma for `accQuad`. -/
lemma accQuad_ext {S T : (SMνCharges n).charges}
    (h : ∀ j, ∑ i, ((fun a => a^2) ∘ toSpecies j S) i =
    ∑ i, ((fun a => a^2) ∘ toSpecies j T) i) :
    accQuad S = accQuad T := by
  rw [accQuad_decomp, accQuad_decomp]
  erw [h 0, h 1, h 2, h 3, h 4]
  rfl

@[simps!]
def cubeTriLin : TriLinearSymm (SMνCharges n).charges where
  toFun S := ∑ i, (6 * ((Q S.1 i) * (Q S.2.1 i) * (Q S.2.2 i))
    + 3 * ((U S.1 i) * (U S.2.1 i) * (U S.2.2 i))
    + 3 * ((D S.1 i) * (D S.2.1 i) * (D S.2.2 i))
    + 2 * ((L S.1 i) * (L S.2.1 i) * (L S.2.2 i))
    +  ((E S.1 i) * (E S.2.1 i) * (E S.2.2 i))
    +  ((N S.1 i) * (N S.2.1 i) * (N S.2.2 i)))
  map_smul₁' a S T R := by
    simp only
    rw [Finset.mul_sum]
    apply Fintype.sum_congr
    intro i
    repeat erw [map_smul]
    simp [HSMul.hSMul, SMul.smul]
    ring
  map_add₁' S T R L := by
    simp only
    rw [← Finset.sum_add_distrib]
    apply Fintype.sum_congr
    intro i
    repeat erw [map_add]
    simp
    ring
  swap₁' S T L := by
    simp
    apply Fintype.sum_congr
    intro i
    ring
  swap₂' S T L := by
    simp
    apply Fintype.sum_congr
    intro i
    ring

lemma cubeTriLin_decomp (S T R : (SMνCharges n).charges) :
    cubeTriLin (S, T, R) = 6 * ∑ i, (Q S i * Q T i * Q R i) + 3 * ∑ i,  (U S i * U T i * U R i) +
      3 * ∑ i,  (D S i * D T i * D R i) + 2 * ∑ i, (L S i * L T i * L R i) +
      ∑ i, (E S i * E T i * E R i) + ∑ i, (N S i * N T i * N R i) := by
  erw [← cubeTriLin.toFun_eq_coe]
  rw [cubeTriLin]
  simp only
  repeat erw [Finset.sum_add_distrib]
  repeat erw [← Finset.mul_sum]


@[simp]
def accCube : HomogeneousCubic (SMνCharges n).charges := cubeTriLin.toCubic

lemma accCube_decomp (S : (SMνCharges n).charges) :
    accCube S = 6 * ∑ i, (Q S i)^3 + 3 * ∑ i, (U S i)^3 + 3 * ∑ i, (D S i)^3 + 2 * ∑ i, (L S i)^3 +
      ∑ i, (E S i)^3 + ∑ i, (N S i)^3 := by
  erw [cubeTriLin_decomp]
  ring_nf

/-- Extensionality lemma for `accCube`. -/
lemma accCube_ext {S T : (SMνCharges n).charges}
    (h : ∀ j, ∑ i, ((fun a => a^3) ∘ toSpecies j S) i =
    ∑ i, ((fun a => a^3) ∘ toSpecies j T) i) :
    accCube S = accCube T := by
  rw [accCube_decomp]
  have h1 : ∀ j, ∑ i, (toSpecies j S i) ^ 3 = ∑ i, (toSpecies j T i) ^ 3 := by
    intro j
    erw [h]
    rfl
  repeat rw [h1]
  rw [accCube_decomp]


end SMνACCs
