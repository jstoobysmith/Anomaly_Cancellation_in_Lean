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
  toFun S := S ⟨18, by simp⟩
  map_add' _ _ := by aesop
  map_smul' _ _ := by aesop

@[simps!]
def Hu : MSSMCharges.charges →ₗ[ℚ] ℚ where
  toFun S := S ⟨19, by simp⟩
  map_add' _ _ := by aesop
  map_smul' _ _ := by aesop

lemma charges_eq_toSpecies_eq (S T : MSSMCharges.charges) :
    S = T ↔ (∀ i, toSMSpecies i S = toSMSpecies i T) ∧ Hd S = Hd T ∧ Hu S = Hu T  := by
  apply Iff.intro
  intro h
  rw [h]
  simp
  intro h
  apply toSpecies.injective
  apply Prod.ext
  funext i
  exact h.1 i
  funext i
  match i with
  | 0 => exact h.2.1
  | 1 => exact h.2.2



lemma Hd_toSpecies_inv (f : (Fin 6 → Fin 3 → ℚ) × (Fin 2 → ℚ)) :
    Hd (toSpecies.symm f) = f.2 0 := by
  rfl

lemma Hu_toSpecies_inv (f : (Fin 6 → Fin 3 → ℚ) × (Fin 2 → ℚ)) :
    Hu (toSpecies.symm f) = f.2 1 := by
  rfl

end MSSMCharges

namespace MSSMACCs

open MSSMCharges

/-- The gravitational anomaly equation. -/
@[simp]
def accGrav : MSSMCharges.charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (6 * Q S i + 3 * U S i + 3 * D S i
    + 2 * L S i + E S i + N S i) + 2 * (Hd S + Hu S)
  map_add' S T := by
    simp only
    repeat rw [map_add]
    simp [mul_add]
    repeat erw [Finset.sum_add_distrib]
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

/-- Extensionality lemma for `accGrav`. -/
lemma accGrav_ext {S T : MSSMCharges.charges}
    (hj : ∀ (j : Fin 6),  ∑ i, (toSMSpecies j) S i = ∑ i, (toSMSpecies j) T i)
    (hd : Hd S = Hd T) (hu : Hu S = Hu T) :
    accGrav S = accGrav T := by
  simp only [accGrav, MSSMSpecies_numberCharges, toSMSpecies_apply, Fin.isValue,
    Fin.reduceFinMk, LinearMap.coe_mk, AddHom.coe_mk]
  repeat erw [Finset.sum_add_distrib]
  repeat erw [← Finset.mul_sum]
  repeat erw [hj]
  rw [hd, hu]
  rfl

/-- The anomaly cancelation condition for SU(2) anomaly. -/
@[simp]
def accSU2 : MSSMCharges.charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (3 * Q S i + L S i) + Hd S + Hu S
  map_add' S T := by
    simp only
    repeat rw [map_add]
    simp [mul_add]
    repeat erw [Finset.sum_add_distrib]
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

/-- Extensionality lemma for `accSU2`. -/
lemma accSU2_ext {S T : MSSMCharges.charges}
    (hj : ∀ (j : Fin 6),  ∑ i, (toSMSpecies j) S i = ∑ i, (toSMSpecies j) T i)
    (hd : Hd S = Hd T) (hu : Hu S = Hu T) :
    accSU2 S = accSU2 T := by
  simp only [accSU2, MSSMSpecies_numberCharges, toSMSpecies_apply, Fin.isValue,
    Fin.reduceFinMk, LinearMap.coe_mk, AddHom.coe_mk]
  repeat erw [Finset.sum_add_distrib]
  repeat erw [← Finset.mul_sum]
  repeat erw [hj]
  rw [hd, hu]
  rfl

/-- The anomaly cancelation condition for SU(3) anomaly. -/
@[simp]
def accSU3 : MSSMCharges.charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (2 * (Q S i) + (U S i) + (D S i))
  map_add' S T := by
    simp only
    repeat rw [map_add]
    simp [mul_add]
    repeat erw [Finset.sum_add_distrib]
    ring
  map_smul' a S := by
    simp only
    repeat rw [(toSMSpecies _).map_smul]
    simp [HSMul.hSMul, SMul.smul]
    repeat erw [Finset.sum_add_distrib]
    repeat erw [← Finset.mul_sum]
    rw [show Rat.cast a = a from rfl]
    ring

/-- Extensionality lemma for `accSU3`. -/
lemma accSU3_ext {S T : MSSMCharges.charges}
    (hj : ∀ (j : Fin 6),  ∑ i, (toSMSpecies j) S i = ∑ i, (toSMSpecies j) T i) :
    accSU3 S = accSU3 T := by
  simp
  repeat erw [Finset.sum_add_distrib]
  repeat erw [← Finset.mul_sum]
  repeat erw [hj]
  rfl

@[simp]
def accYY : MSSMCharges.charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, ((Q S) i + 8 * (U S) i + 2 * (D S) i + 3 * (L S) i
    + 6 * (E S) i) + 3 * (Hd S + Hu S)
  map_add' S T := by
    simp only
    repeat rw [map_add]
    simp [mul_add]
    repeat erw [Finset.sum_add_distrib]
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

/-- Extensionality lemma for `accGrav`. -/
lemma accYY_ext {S T : MSSMCharges.charges}
    (hj : ∀ (j : Fin 6),  ∑ i, (toSMSpecies j) S i = ∑ i, (toSMSpecies j) T i)
    (hd : Hd S = Hd T) (hu : Hu S = Hu T) :
    accYY S = accYY T := by
  simp only [accYY, MSSMSpecies_numberCharges, toSMSpecies_apply, Fin.isValue,
    Fin.reduceFinMk, LinearMap.coe_mk, AddHom.coe_mk]
  repeat erw [Finset.sum_add_distrib]
  repeat erw [← Finset.mul_sum]
  repeat erw [hj]
  rw [hd, hu]
  rfl


@[simps!]
def quadBiLin  : BiLinearSymm MSSMCharges.charges where
  toFun S := ∑ i, (Q S.1 i *  Q S.2 i + (- 2) * (U S.1 i *  U S.2 i) +
    D S.1 i *  D S.2 i + (- 1) * (L S.1 i * L S.2 i)  + E S.1 i * E S.2 i) +
    (- Hd S.1 * Hd S.2 + Hu S.1 * Hu S.2)
  map_smul₁' a S T := by
    simp only
    rw [mul_add]
    congr 1
    rw [Finset.mul_sum]
    apply Fintype.sum_congr
    intro i
    repeat erw [map_smul]
    simp [HSMul.hSMul, SMul.smul]
    ring
    simp
    ring
  map_add₁' S T R := by
    simp only
    rw [add_assoc, ← add_assoc (-Hd S * Hd R + Hu S * Hu R) _ _]
    rw [add_comm (-Hd S * Hd R + Hu S * Hu R) _]
    rw [add_assoc]
    rw [← add_assoc _ _ (-Hd S * Hd R + Hu S * Hu R + (-Hd T * Hd R + Hu T * Hu R))]
    congr 1
    rw [← Finset.sum_add_distrib]
    apply Fintype.sum_congr
    intro i
    repeat erw [map_add]
    simp
    ring
    rw [Hd.map_add, Hu.map_add]
    ring
  swap' S L := by
    simp
    congr 1
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    simp
    ring
    ring

@[simp]
def accQuad : HomogeneousQuadratic MSSMCharges.charges := quadBiLin.toHomogeneousQuad

/-- Extensionality lemma for `accQuad`. -/
lemma accQuad_ext {S T : (MSSMCharges).charges}
    (h : ∀ j, ∑ i, ((fun a => a^2) ∘ toSMSpecies j S) i =
    ∑ i, ((fun a => a^2) ∘ toSMSpecies j T) i)
    (hd : Hd S = Hd T) (hu : Hu S = Hu T) :
    accQuad S = accQuad T := by
  simp only [accQuad, BiLinearSymm.toHomogeneousQuad_toFun]
  erw [← quadBiLin.toFun_eq_coe]
  rw [quadBiLin]
  simp only
  repeat erw [Finset.sum_add_distrib]
  repeat erw [← Finset.mul_sum]
  ring_nf
  have h1 : ∀ j, ∑ i, (toSMSpecies j S i)^2 = ∑ i, (toSMSpecies j T i)^2 := by
    intro j
    erw [h]
    rfl
  repeat rw [h1]
  rw [hd, hu]


@[simp]
def cubeTriLinToFun
    (S : MSSMCharges.charges × MSSMCharges.charges × MSSMCharges.charges) : ℚ :=
  ∑ i, (6 * (Q S.1 i * Q S.2.1 i * Q S.2.2 i)
    + 3 * (U S.1 i * U S.2.1 i * U S.2.2 i)
    + 3 * (D S.1 i * D S.2.1 i * D S.2.2 i)
    + 2 * (L S.1 i * L S.2.1 i * L S.2.2 i)
    + E S.1 i * E S.2.1 i * E S.2.2 i
    + N S.1 i * N S.2.1 i * N S.2.2 i)
    + (2 * Hd S.1 * Hd S.2.1 * Hd S.2.2
    + 2 * Hu S.1 * Hu S.2.1 * Hu S.2.2)

lemma cubeTriLinToFun_map_smul₁ (a : ℚ)  (S T R : MSSMCharges.charges) :
    cubeTriLinToFun (a • S, T, R) = a * cubeTriLinToFun (S, T, R) := by
  simp only [cubeTriLinToFun]
  rw [mul_add]
  congr 1
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro i
  repeat erw [map_smul]
  simp [HSMul.hSMul, SMul.smul]
  ring
  simp
  ring


lemma cubeTriLinToFun_map_add₁ (S T R L : MSSMCharges.charges) :
    cubeTriLinToFun (S + T, R, L) = cubeTriLinToFun (S, R, L) + cubeTriLinToFun (T, R, L) := by
  simp only [cubeTriLinToFun]
  rw [add_assoc, ← add_assoc (2 * Hd S * Hd R * Hd L + 2 * Hu S * Hu R * Hu L) _ _]
  rw [add_comm (2 * Hd S * Hd R * Hd L + 2 * Hu S * Hu R * Hu L) _]
  rw [add_assoc]
  rw [← add_assoc _ _  (2 * Hd S * Hd R * Hd L + 2 * Hu S * Hu R * Hu L +
   (2 * Hd T * Hd R * Hd L + 2 * Hu T * Hu R * Hu L))]
  congr 1
  rw [← Finset.sum_add_distrib]
  apply Fintype.sum_congr
  intro i
  repeat erw [map_add]
  simp
  ring
  rw [Hd.map_add, Hu.map_add]
  ring


lemma cubeTriLinToFun_swap1 (S T R : MSSMCharges.charges) :
    cubeTriLinToFun (S, T, R) = cubeTriLinToFun (T, S, R) := by
  simp
  congr 1
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp
  ring
  ring

lemma cubeTriLinToFun_swap2 (S T R : MSSMCharges.charges) :
    cubeTriLinToFun (S, T, R) = cubeTriLinToFun (S, R, T) := by
  simp
  congr 1
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  simp
  ring
  ring

def cubeTriLin : TriLinearSymm MSSMCharges.charges where
  toFun S := cubeTriLinToFun S
  map_smul₁' := cubeTriLinToFun_map_smul₁
  map_add₁' := cubeTriLinToFun_map_add₁
  swap₁' := cubeTriLinToFun_swap1
  swap₂' := cubeTriLinToFun_swap2

@[simp]
def accCube : HomogeneousCubic MSSMCharges.charges := cubeTriLin.toCubic

/-- Extensionality lemma for `accCube`. -/
lemma accCube_ext {S T : MSSMCharges.charges}
    (h : ∀ j, ∑ i, ((fun a => a^3) ∘ toSMSpecies j S) i =
    ∑ i, ((fun a => a^3) ∘ toSMSpecies j T) i)
    (hd : Hd S = Hd T) (hu : Hu S = Hu T)  :
    accCube S = accCube T := by
  simp [cubeTriLin, cubeTriLinToFun]
  erw [← cubeTriLin.toFun_eq_coe]
  rw [cubeTriLin]
  simp only [cubeTriLinToFun]
  repeat erw [Finset.sum_add_distrib]
  repeat erw [← Finset.mul_sum]
  ring_nf
  have h1 : ∀ j, ∑ i, (toSMSpecies j S i)^3 = ∑ i, (toSMSpecies j T i)^3 := by
    intro j
    erw [h]
    rfl
  repeat rw [h1]
  rw [hd, hu]

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
lemma quadSol  (S : MSSMACC.QuadSols) : accQuad S.val = 0 := by
  have hS := S.quadSol
  simp  [MSSMACCs.accQuad, HomogeneousQuadratic.toFun] at hS
  exact hS 0

@[simp]
def AnomalyFreeMk (S : MSSMACC.charges) (hg : accGrav S = 0)
    (hsu2 : accSU2 S = 0) (hsu3 : accSU3 S = 0) (hyy : accYY S = 0)
    (hquad : accQuad S = 0) (hcube : accCube S = 0) : MSSMACC.Sols :=
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
def AnomalyFreeQuadMk' (S : MSSMACC.LinSols) (hquad : accQuad S.val = 0) :
    MSSMACC.QuadSols :=
  ⟨S, by
    intro i
    simp at i
    match i with
    | 0 => exact hquad
    ⟩

@[simp]
def AnomalyFreeMk' (S : MSSMACC.LinSols) (hquad : accQuad S.val = 0)
    (hcube : accCube S.val = 0) : MSSMACC.Sols :=
  ⟨⟨S, by
    intro i
    simp at i
    match i with
    | 0 => exact hquad
    ⟩ , by exact hcube ⟩

@[simp]
def AnomalyFreeMk'' (S : MSSMACC.QuadSols)
    (hcube : accCube S.val = 0) : MSSMACC.Sols :=
  ⟨S , by exact hcube ⟩

lemma AnomalyFreeMk''_val (S : MSSMACC.QuadSols)
    (hcube : accCube S.val = 0) :
    (AnomalyFreeMk'' S hcube).val = S.val := by
  rfl

-- TODO: to be moved
@[simps!]
def dot  : BiLinearSymm MSSMCharges.charges where
  toFun S := ∑ i, (Q S.1 i *  Q S.2 i +  U S.1 i *  U S.2 i +
    D S.1 i *  D S.2 i + L S.1 i * L S.2 i  + E S.1 i * E S.2 i
    + N S.1 i * N S.2 i) + Hd S.1 * Hd S.2 + Hu S.1 * Hu S.2
  map_smul₁' a S T := by
    simp only [MSSMSpecies_numberCharges]
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
  swap' S L := by
    simp
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    simp
    ring

end MSSMACC
