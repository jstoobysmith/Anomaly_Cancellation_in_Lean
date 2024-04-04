/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.MSSM.Basic
import Mathlib.Tactic.Polyrith
-- Reference : https://arxiv.org/pdf/2107.07926.pdf

universe v u

namespace MSSMACC
open MSSMCharges
open MSSMACCs
open BigOperators

def Y₃AsCharge : MSSMACC.charges := toSpecies.symm
  ⟨fun s => fun i =>
    match s, i with
    | 0, 0 => 1
    | 0, 1 => 1
    | 0, 2 => - 1
    | 1, 0 => -4
    | 1, 1 => -4
    | 1, 2 => 4
    | 2, 0 => 2
    | 2, 1 => 2
    | 2, 2 => - 2
    | 3, 0 => -3
    | 3, 1 => -3
    | 3, 2 => 3
    | 4, 0 => 6
    | 4, 1 => 6
    | 4, 2 => - 6
    | 5, 0 => 0
    | 5, 1 => 0
    | 5, 2 => 0,
  fun s =>
    match s with
    | 0 => -3
    | 1 => 3⟩

def Y₃ : MSSMACC.AnomalyFree :=
  MSSMACC.AnomalyFreeMk Y₃AsCharge (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)

lemma Y₃_val : Y₃.val = Y₃AsCharge := by
  rfl

lemma doublePoint_Y₃_Y₃ (R : MSSMACC.AnomalyFreeLinear) :
    cubeTriLin (Y₃.val, Y₃.val, R.val) = 0 := by
  rw [← TriLinearSymm.toFun_eq_coe]
  simp only [cubeTriLin, cubeTriLinToFun, MSSMSpecies_numberCharges]
  rw [Fin.sum_univ_three]
  rw [Y₃_val]
  rw [Y₃AsCharge]
  repeat rw [toSMSpecies_toSpecies_inv]
  rw [Hd_toSpecies_inv, Hu_toSpecies_inv]
  simp
  have hLin := R.linearSol
  simp at hLin
  have h3 := hLin 3
  simp [Fin.sum_univ_three] at h3
  linear_combination 6 * h3

def B₃AsCharge : MSSMACC.charges := toSpecies.symm
  ⟨fun s => fun i =>
    match s, i with
    | 0, 0 => 1
    | 0, 1 => 1
    | 0, 2 => - 1
    | 1, 0 => - 1
    | 1, 1 => - 1
    | 1, 2 =>  1
    | 2, 0 => - 1
    | 2, 1 => - 1
    | 2, 2 =>  1
    | 3, 0 => - 3
    | 3, 1 => - 3
    | 3, 2 => 3
    | 4, 0 => 3
    | 4, 1 => 3
    | 4, 2 => - 3
    | 5, 0 => 3
    | 5, 1 => 3
    | 5, 2 => - 3,
  fun s =>
    match s with
    | 0 => -3
    | 1 => 3⟩


def B₃ : MSSMACC.AnomalyFree :=
  MSSMACC.AnomalyFreeMk B₃AsCharge (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)

lemma B₃_val : B₃.val = B₃AsCharge := by
  rfl

lemma doublePoint_B₃_B₃ (R : MSSMACC.AnomalyFreeLinear) :
    cubeTriLin (B₃.val, B₃.val, R.val) = 0 := by
  rw [← TriLinearSymm.toFun_eq_coe]
  simp only [cubeTriLin, cubeTriLinToFun, MSSMSpecies_numberCharges]
  rw [Fin.sum_univ_three]
  rw [B₃_val]
  rw [B₃AsCharge]
  repeat rw [toSMSpecies_toSpecies_inv]
  rw [Hd_toSpecies_inv, Hu_toSpecies_inv]
  simp
  have hLin := R.linearSol
  simp at hLin
  have h0 := hLin 0
  have h2 := hLin 2
  simp [Fin.sum_univ_three] at h0 h2
  linear_combination 9 * h0 - 24 * h2

def lineY₃B₃Charges (a b : ℚ) : MSSMACC.AnomalyFreeLinear := a • Y₃.1.1 + b • B₃.1.1

lemma lineY₃B₃Charges_quad (a b : ℚ) : accQuad (lineY₃B₃Charges a b).val = 0 := by
  change accQuad (a • Y₃.val + b • B₃.val) = 0
  rw [accQuad]
  rw [quadBiLin.toHomogeneousQuad_add]
  rw [quadBiLin.toHomogeneousQuad.map_smul]
  rw [quadBiLin.toHomogeneousQuad.map_smul]
  rw [quadBiLin.map_smul₁, quadBiLin.map_smul₂]
  erw [quadSol Y₃.1, quadSol B₃.1]
  simp
  apply Or.inr ∘ Or.inr
  rfl

lemma lineY₃B₃Charges_cubic (a b : ℚ) : accCube (lineY₃B₃Charges a b).val = 0 := by
  change accCube (a • Y₃.val + b • B₃.val) = 0
  rw [accCube]
  rw [cubeTriLin.toCubic_add]
  rw [cubeTriLin.toCubic.map_smul]
  rw [cubeTriLin.toCubic.map_smul]
  rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₂, cubeTriLin.map_smul₃]
  rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₂, cubeTriLin.map_smul₃]
  erw [Y₃.cubicSol,  B₃.cubicSol]
  rw [show cubeTriLin (Y₃.val, Y₃.val, B₃.val) = 0 by rfl]
  rw [show cubeTriLin (B₃.val, B₃.val, Y₃.val) = 0 by rfl]
  simp

def lineY₃B₃ (a b : ℚ) : MSSMACC.AnomalyFree :=
  AnomalyFreeMk' (lineY₃B₃Charges a b) (lineY₃B₃Charges_quad a b) (lineY₃B₃Charges_cubic a b)

lemma doublePoint_Y₃_B₃ (R : MSSMACC.AnomalyFreeLinear) :
    cubeTriLin (Y₃.val, B₃.val, R.val) = 0 := by
  rw [← TriLinearSymm.toFun_eq_coe]
  simp only [cubeTriLin, cubeTriLinToFun, MSSMSpecies_numberCharges]
  rw [Fin.sum_univ_three]
  rw [B₃_val, Y₃_val]
  rw [B₃AsCharge, Y₃AsCharge]
  repeat rw [toSMSpecies_toSpecies_inv]
  rw [Hd_toSpecies_inv, Hu_toSpecies_inv]
  rw [Hd_toSpecies_inv, Hu_toSpecies_inv]
  simp
  have hLin := R.linearSol
  simp at hLin
  have h1 := hLin 1
  have h2 := hLin 2
  have h3 := hLin 3
  simp [Fin.sum_univ_three] at h1 h2 h3
  linear_combination -(12 * h2) + 9 * h1 + 3 * h3

lemma lineY₃B₃_doublePoint (R : MSSMACC.AnomalyFreeLinear) (a b : ℚ) :
    cubeTriLin ((lineY₃B₃ a b).val, (lineY₃B₃ a b).val, R.val) = 0 := by
  change cubeTriLin (a • Y₃.val + b • B₃.val , a • Y₃.val + b • B₃.val, R.val ) = 0
  rw [cubeTriLin.map_add₂, cubeTriLin.map_add₁, cubeTriLin.map_add₁]
  repeat rw [cubeTriLin.map_smul₂, cubeTriLin.map_smul₁]
  rw [doublePoint_B₃_B₃, doublePoint_Y₃_Y₃, doublePoint_Y₃_B₃]
  rw [cubeTriLin.swap₁, doublePoint_Y₃_B₃]
  simp



end MSSMACC
