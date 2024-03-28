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
# Anomaly cancellation conditions for n families with RHN.

-/

universe v u
open Nat
open BigOperators

@[simps!]
def MSSMCharges : ACCSystemCharges := ACCSystemChargesMk 20

@[simps!]
def MSSMSpecies : ACCSystemCharges := ACCSystemChargesMk 3

namespace MSSMCharges
@[simps!]
def toSMPlusH : MSSMCharges.charges ≃ (Fin 18 ⊕ Fin 2 → ℚ) :=
  ((@finSumFinEquiv 18 2).arrowCongr (Equiv.refl ℚ)).symm

@[simps!]
def splitSMPlusH : (Fin 18 ⊕ Fin 2 → ℚ) ≃ (Fin 18 → ℚ) × (Fin 2 → ℚ) where
  toFun f := (f ∘ Sum.inl , f ∘ Sum.inr)
  invFun f :=  Sum.elim f.1 f.2
  left_inv f := by
    aesop
  right_inv f := by
    aesop

@[simps!]
def toSplitSMPlusH  : MSSMCharges.charges ≃ (Fin 18 → ℚ) × (Fin 2 → ℚ) :=
  toSMPlusH.trans splitSMPlusH

@[simps!]
def toSpeciesMaps' : (Fin 18 → ℚ) ≃ (Fin 6 → Fin 3 → ℚ) :=
   ((Equiv.curry _ _ _).symm.trans
    ((@finProdFinEquiv 6 3).arrowCongr (Equiv.refl ℚ))).symm

@[simps!]
def toSpecies : MSSMCharges.charges ≃ (Fin 6 → Fin 3 → ℚ) × (Fin 2 → ℚ) :=
  toSplitSMPlusH.trans (Equiv.prodCongr toSpeciesMaps' (Equiv.refl _))

@[simps!]
def toSMSpecies (i : Fin 6) : MSSMCharges.charges →ₗ[ℚ] MSSMSpecies.charges where
  toFun S := (Prod.fst ∘ toSpecies) S i
  map_add' _ _ := by aesop
  map_smul' _ _ := by aesop

lemma toSMSpecies_toSpecies_inv (i : Fin 6) (f :  (Fin 6 → Fin 3 → ℚ) × (Fin 2 → ℚ)) :
    (toSMSpecies i) (toSpecies.symm f) = f.1 i := by
  change (Prod.fst ∘ toSpecies ∘ toSpecies.symm ) _ i= f.1 i
  simp


abbrev Q := toSMSpecies 0
abbrev U := toSMSpecies 1
abbrev D := toSMSpecies 2
abbrev L := toSMSpecies 3
abbrev E := toSMSpecies 4
abbrev N := toSMSpecies 5

@[simps!]
def Hd : MSSMCharges.charges →ₗ[ℚ] ℚ where
  toFun S := S 18
  map_add' _ _ := by aesop
  map_smul' _ _ := by aesop

@[simps!]
def Hu : MSSMCharges.charges →ₗ[ℚ] ℚ where
  toFun S := S 19
  map_add' _ _ := by aesop
  map_smul' _ _ := by aesop

lemma Hd_toSpecies_inv (f : (Fin 6 → Fin 3 → ℚ) × (Fin 2 → ℚ)) :
    Hd (toSpecies.symm f) = f.2 0 := by
  rfl

lemma Hu_toSpecies_inv (f : (Fin 6 → Fin 3 → ℚ) × (Fin 2 → ℚ)) :
    Hu (toSpecies.symm f) = f.2 1 := by
  rfl

end MSSMCharges

namespace MSSMACCs

open MSSMCharges

@[simp]
def accGrav : MSSMCharges.charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (6 * Q S i + 3 * U S i + 3 * D S i
    + 2 * L S i + E S i + N S i) + 2 * (Hd S + Hu S)
  map_add' S T := by
    simp
    repeat erw [AddHom.map_add]
    rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
    simp
    ring
  map_smul' a S := by
    simp only
    repeat rw [(toSMSpecies _).map_smul]
    erw [Hd.map_smul, Hu.map_smul]
    simp [HSMul.hSMul, SMul.smul]
    repeat erw [Finset.sum_add_distrib]
    repeat erw [← Finset.mul_sum]
    rw [show Rat.cast a = a from rfl]
    ring

/-- The anomaly cancelation condition for SU(2) anomaly. -/
@[simp]
def accSU2 : MSSMCharges.charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (3 * Q S i + L S i) + Hd S + Hu S
  map_add' S T := by
    simp
    repeat erw [AddHom.map_add]
    rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
    simp
    ring
  map_smul' a S := by
    simp only
    repeat rw [(toSMSpecies _).map_smul]
    erw [Hd.map_smul, Hu.map_smul]
    simp [HSMul.hSMul, SMul.smul]
    repeat erw [Finset.sum_add_distrib]
    repeat erw [← Finset.mul_sum]
    rw [show Rat.cast a = a from rfl]
    ring

/-- The anomaly cancelation condition for SU(3) anomaly. -/
@[simp]
def accSU3 : MSSMCharges.charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (2 * (Q S i) + (U S i) + (D S i))
  map_add' S T := by
    simp
    repeat erw [AddHom.map_add]
    rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
    simp
    ring
  map_smul' a S := by
    simp only
    repeat rw [(toSMSpecies _).map_smul]
    simp [HSMul.hSMul, SMul.smul]
    repeat erw [Finset.sum_add_distrib]
    repeat erw [← Finset.mul_sum]
    rw [show Rat.cast a = a from rfl]
    ring

@[simp]
def accYY : MSSMCharges.charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, ((Q S) i + 8 * (U S) i + 2 * (D S) i + 3 * (L S) i
    + 6 * (E S) i) + 3 * (Hd S + Hu S)
  map_add' S T := by
    simp
    repeat erw [AddHom.map_add]
    rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
    simp
    ring
  map_smul' a S := by
    simp only
    repeat rw [(toSMSpecies _).map_smul]
    erw [Hd.map_smul, Hu.map_smul]
    simp [HSMul.hSMul, SMul.smul]
    repeat erw [Finset.sum_add_distrib]
    repeat erw [← Finset.mul_sum]
    rw [show Rat.cast a = a from rfl]
    ring


@[simps!]
def quadBiLin  : BiLinearSymm MSSMCharges.charges where
  toFun S := ∑ i, (Q S.1 i *  Q S.2 i + (- 2) * (U S.1 i *  U S.2 i) +
    D S.1 i *  D S.2 i + (- (L S.1 i * L S.2 i))  + E S.1 i * E S.2 i)
    - Hd S.1 * Hd S.2 + Hu S.1 * Hu S.2
  map_smul₁' a S T := by
    simp only
    repeat rw [(toSMSpecies _).map_smul]
    rw [Hd.map_smul, Hu.map_smul]
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    simp [HSMul.hSMul, SMul.smul]
    ring
  map_smul₂' a S T := by
    simp only
    repeat rw [(toSMSpecies _).map_smul]
    rw [Hd.map_smul, Hu.map_smul]
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    simp [HSMul.hSMul, SMul.smul]
    ring
  map_add₁' S T R := by
    simp
    repeat erw [AddHom.map_add]
    rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
    simp
    ring
  map_add₂' S T L := by
    simp
    repeat erw [AddHom.map_add]
    rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
    simp
    ring
  swap' S L := by
    simp
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    simp
    ring

@[simp]
def accQuad : HomogeneousQuadratic MSSMCharges.charges := quadBiLin.toHomogeneousQuad


@[simp]
def cubeTriLinToFun
    (S : MSSMCharges.charges × MSSMCharges.charges × MSSMCharges.charges) : ℚ :=
  ∑ i, (6 * (Q S.1 i * Q S.2.1 i * Q S.2.2 i) + 3 * (U S.1 i * U S.2.1 i * U S.2.2 i)
    + 3 * (D S.1 i * D S.2.1 i * D S.2.2 i) + 2 * (L S.1 i * L S.2.1 i * L S.2.2 i)
    + E S.1 i * E S.2.1 i * E S.2.2 i + N S.1 i * N S.2.1 i * N S.2.2 i)
  + 2 * (Hd S.1 * Hd S.2.1 * Hd S.2.2 + Hu S.1 * Hu S.2.1 * Hu S.2.2)

lemma cubeTriLinToFun_map_smul₁ (a : ℚ)  (S T R : MSSMCharges.charges) :
    cubeTriLinToFun (a • S, T, R) = a * cubeTriLinToFun (S, T, R) := by
  simp only [cubeTriLinToFun]
  repeat rw [(toSMSpecies _).map_smul]
  rw [Hd.map_smul, Hu.map_smul]
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp [HSMul.hSMul, SMul.smul]
  ring

lemma cubeTriLinToFun_map_smul₂ (a : ℚ) (S T R : MSSMCharges.charges) :
    cubeTriLinToFun (S, a • T, R) = a * cubeTriLinToFun (S, T, R) := by
  simp only [cubeTriLinToFun]
  repeat rw [(toSMSpecies _).map_smul]
  rw [Hd.map_smul, Hu.map_smul]
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp [HSMul.hSMul, SMul.smul]
  ring

lemma cubeTriLinToFun_map_smul₃ (a : ℚ) (S T R : MSSMCharges.charges) :
    cubeTriLinToFun (S, T, a • R) = a * cubeTriLinToFun (S, T, R) := by
  simp only [cubeTriLinToFun]
  repeat rw [(toSMSpecies _).map_smul]
  rw [Hd.map_smul, Hu.map_smul]
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp [HSMul.hSMul, SMul.smul]
  ring

lemma cubeTriLinToFun_map_add₁ (S T R L : MSSMCharges.charges) :
    cubeTriLinToFun (S + T, R, L) = cubeTriLinToFun (S, R, L) + cubeTriLinToFun (T, R, L) := by
  simp only [cubeTriLinToFun]
  repeat erw [AddHom.map_add]
  rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
  simp
  ring

lemma cubeTriLinToFun_map_add₂ (S T R L : MSSMCharges.charges) :
    cubeTriLinToFun (S, T + R, L) = cubeTriLinToFun (S, T, L) + cubeTriLinToFun (S, R, L) := by
  simp only [cubeTriLinToFun]
  repeat erw [AddHom.map_add]
  rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
  simp
  ring

lemma cubeTriLinToFun_map_add₃ (S T R L : MSSMCharges.charges) :
    cubeTriLinToFun (S, T, R + L) = cubeTriLinToFun (S, T, R) + cubeTriLinToFun (S, T, L) := by
  simp only [cubeTriLinToFun]
  repeat erw [AddHom.map_add]
  rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
  simp
  ring

lemma cubeTriLinToFun_swap1 (S T R : MSSMCharges.charges) :
    cubeTriLinToFun (S, T, R) = cubeTriLinToFun (T, S, R) := by
  simp
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp
  ring

lemma cubeTriLinToFun_swap2 (S T R : MSSMCharges.charges) :
    cubeTriLinToFun (S, T, R) = cubeTriLinToFun (S, R, T) := by
  simp
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp
  ring

def cubeTriLin : TriLinearSymm MSSMCharges.charges where
  toFun S := cubeTriLinToFun S
  map_smul₁' := cubeTriLinToFun_map_smul₁
  map_smul₂' := cubeTriLinToFun_map_smul₂
  map_smul₃' := cubeTriLinToFun_map_smul₃
  map_add₁' := cubeTriLinToFun_map_add₁
  map_add₂' := cubeTriLinToFun_map_add₂
  map_add₃' := cubeTriLinToFun_map_add₃
  swap₁' := cubeTriLinToFun_swap1
  swap₂' := cubeTriLinToFun_swap2

@[simp]
def accCube : HomogeneousCubic MSSMCharges.charges := cubeTriLin.toCubic

end MSSMACCs

open MSSMACCs

@[simps!]
def MSSMACC : ACCSystem where
  numberLinear := 4
  linearACCs := fun i =>
    match i with
    | 0 => accGrav
    | 1 => accSU2
    | 2 => accSU3
    | 3 => accYY
  numberQuadratic := 1
  quadraticACCs := fun i =>
    match i with
    | 0 => accQuad
  cubicACC := accCube

namespace MSSMACC
open MSSMCharges
lemma quadSol  (S : MSSMACC.AnomalyFreeQuad) : accQuad S.val = 0 := by
  have hS := S.quadSol
  simp  [MSSMACCs.accQuad, HomogeneousQuadratic.toFun] at hS
  exact hS 0

@[simp]
def AnomalyFreeMk (S : MSSMACC.charges) (hg : accGrav S = 0)
    (hsu2 : accSU2 S = 0) (hsu3 : accSU3 S = 0) (hyy : accYY S = 0)
    (hquad : accQuad S = 0) (hcube : accCube S = 0) : MSSMACC.AnomalyFree :=
  ⟨⟨⟨S, by
    intro i
    simp at i
    match i with
    | 0 => exact hg
    | 1 => exact hsu2
    | 2 => exact hsu3
    | 3 => exact hyy⟩, by
    intro i
    simp at i
    match i with
    | 0 => exact hquad
    ⟩ , by exact hcube ⟩

lemma AnomalyFreeMk_val (S : MSSMACC.charges) (hg : accGrav S = 0)
    (hsu2 : accSU2 S = 0) (hsu3 : accSU3 S = 0) (hyy : accYY S = 0)
    (hquad : accQuad S = 0) (hcube : accCube S = 0) :
    (AnomalyFreeMk S hg hsu2 hsu3 hyy hquad hcube).val = S := by
  rfl

@[simp]
def AnomalyFreeQuadMk' (S : MSSMACC.AnomalyFreeLinear) (hquad : accQuad S.val = 0) :
    MSSMACC.AnomalyFreeQuad :=
  ⟨S, by
    intro i
    simp at i
    match i with
    | 0 => exact hquad
    ⟩


@[simp]
def AnomalyFreeMk' (S : MSSMACC.AnomalyFreeLinear) (hquad : accQuad S.val = 0)
    (hcube : accCube S.val = 0) : MSSMACC.AnomalyFree :=
  ⟨⟨S, by
    intro i
    simp at i
    match i with
    | 0 => exact hquad
    ⟩ , by exact hcube ⟩

@[simp]
def AnomalyFreeMk'' (S : MSSMACC.AnomalyFreeQuad)
    (hcube : accCube S.val = 0) : MSSMACC.AnomalyFree :=
  ⟨S , by exact hcube ⟩

lemma AnomalyFreeMk''_val (S : MSSMACC.AnomalyFreeQuad)
    (hcube : accCube S.val = 0) :
    (AnomalyFreeMk'' S hcube).val = S.val := by
  rfl

@[simps!]
def dot  : BiLinearSymm MSSMCharges.charges where
  toFun S := ∑ i, (Q S.1 i *  Q S.2 i +  U S.1 i *  U S.2 i +
    D S.1 i *  D S.2 i + L S.1 i * L S.2 i  + E S.1 i * E S.2 i
    + N S.1 i * N S.2 i) + Hd S.1 * Hd S.2 + Hu S.1 * Hu S.2
  map_smul₁' a S T := by
    simp only
    repeat rw [(toSMSpecies _).map_smul]
    rw [Hd.map_smul, Hu.map_smul]
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    simp [HSMul.hSMul, SMul.smul]
    ring
  map_smul₂' a S T := by
    simp only
    repeat rw [(toSMSpecies _).map_smul]
    rw [Hd.map_smul, Hu.map_smul]
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    simp [HSMul.hSMul, SMul.smul]
    ring
  map_add₁' S T R := by
    simp
    repeat erw [AddHom.map_add]
    rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
    simp
    ring
  map_add₂' S T L := by
    simp
    repeat erw [AddHom.map_add]
    rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
    simp
    ring
  swap' S L := by
    simp
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    simp
    ring
end MSSMACC
