/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.SMRHN.PlusU1.Basic
import AnomalyCancellationInLean.SMRHN.PlusU1.FamilyMaps

universe v u

namespace SMRHN
namespace PlusU1

open SMνCharges
open SMνACCs
open BigOperators

variable {n : ℕ}

@[simps!]
def BL₁ : (PlusU1 1).AnomalyFree where
  val := fun i =>
    match i with
    | 0 => 1
    | 1 => -1
    | 2 => -1
    | 3 => -3
    | 4 => 3
    | 5 => 3
  linearSol := by
    intro i
    simp at i
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl
  quadSol := by
    intro i
    simp at i
    match i with
    | 0 => rfl
  cubicSol := by rfl

@[simps!]
def BL (n : ℕ) : (PlusU1 n).AnomalyFree :=
  familyUniversalAF n BL₁

namespace BL

variable {n : ℕ}

lemma on_quadBiLin (S : (PlusU1 n).charges) :
    quadBiLin ((BL n).val, S) = 1/2 * accYY S + 3/2 * accSU2 S - 2 * accSU3 S := by
  erw [familyUniversal_quadBiLin]
  rw [accYY_decomp, accSU2_decomp, accSU3_decomp]
  simp
  ring

lemma on_quadBiLin_AFL (S : (PlusU1 n).AnomalyFreeLinear) : quadBiLin ((BL n).val, S.val) = 0 := by
  rw [on_quadBiLin]
  rw [YYsol S, SU2Sol S, SU3Sol S]
  simp

lemma add_AFL_quad (S : (PlusU1 n).AnomalyFreeLinear) (a b : ℚ) :
    accQuad (a • S.val + b • (BL n).val) = a ^ 2 * accQuad S.val := by
  erw [BiLinearSymm.toHomogeneousQuad_add, quadSol (b • (BL n)).1]
  rw [quadBiLin.map_smul₁, quadBiLin.map_smul₂, quadBiLin.swap, on_quadBiLin_AFL]
  erw [accQuad.map_smul]
  simp

lemma add_quad (S : (PlusU1 n).AnomalyFreeQuad) (a b : ℚ) :
    accQuad (a • S.val + b • (BL n).val) = 0 := by
  rw [add_AFL_quad, quadSol S]
  simp

def addQuad (S : (PlusU1 n).AnomalyFreeQuad) (a b : ℚ) : (PlusU1 n).AnomalyFreeQuad :=
  linearToQuad (a • S.1 + b • (BL n).1.1) (add_quad S a b)

lemma addQuad_zero (S : (PlusU1 n).AnomalyFreeQuad) (a : ℚ): addQuad S a 0 = a • S := by
  simp [addQuad, linearToQuad]
  rfl

lemma on_cubeTriLin (S : (PlusU1 n).charges) :
    cubeTriLin ((BL n).val, (BL n).val, S) = 9 * accGrav S - 24 * accSU3 S := by
  erw [familyUniversal_cubeTriLin']
  rw [accGrav_decomp, accSU3_decomp]
  simp
  ring

lemma on_cubeTriLin_AFL (S : (PlusU1 n).AnomalyFreeLinear) :
    cubeTriLin ((BL n).val, (BL n).val, S.val) = 0 := by
  rw [on_cubeTriLin]
  rw [gravSol S, SU3Sol S]
  simp

lemma add_AFL_cube (S : (PlusU1 n).AnomalyFreeLinear) (a b : ℚ) :
    accCube (a • S.val + b • (BL n).val) =
    a ^ 2 * (a * accCube S.val + 3 * b * cubeTriLin (S.val, S.val, (BL n).val)) := by
  erw [TriLinearSymm.toCubic_add, cubeSol (b • (BL n)), accCube.map_smul]
  repeat rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₂, cubeTriLin.map_smul₃]
  rw [on_cubeTriLin_AFL]
  simp
  ring


end BL
end PlusU1
end SMRHN
