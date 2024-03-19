/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.SMRHNPlusU1.BMinusL


universe v u

namespace SMRHNPlusU1
open SMRHNPlusU1Charges
open SMRHNPlusU1ACCs
open BigOperators

namespace QuadToCubic

def generic {n : ℕ} (S : AnomalyFreeQuad) : AnomalyFree :=
  ⟨AnomalyFreeQuadAddBMinusL (accCube S.val.val)
  (AnomalyFreeQuadSmul (- 3 * accCubeDiv BMinusL.val.val.val S.val.val) S),
  by
   simp only [AnomalyFreeQuadAddBMinusL, AnomalyFreeQuadSmul, HAdd.hAdd]
   simp only [Add.add]
   simp only [HSMul.hSMul]
   simp only [SMul.smul]
   rw [accCube_add, accCube_smul, accCube_smul, accCubeDiv_smul_left,
   accCubeDiv_smul_left, accCubeDiv_smul_right, accCubeDiv_smul_right]
   rw [BMinusL.Cube, accCubeDiv_AnomalyFreeLinear_BMinusL]
   ring
  ⟩

lemma mapToCubeGeneric_on_cube (S : AnomalyFree) :
    mapToCubeGeneric S.val =
     AnomalyFreeSMul (- 3 * accCubeDiv BMinusL.val.val.val S.val.val.val) S := by
  rw [mapToCubeGeneric]
  apply AnomalyFree.ext
  simp only
  rw [S.Cube]
  rw [AnomalyFreeQuadAddBMinusL_zero]
  rfl

def mapToCubeSpecial (S : AnomalyFreeQuad) (hSSS : accCube S.val.val = 0)
    (hB : accCubeDiv BMinusL.val.val.val S.val.val = 0) (a b : ℚ) : AnomalyFree :=
  ⟨AnomalyFreeQuadAddBMinusL a (AnomalyFreeQuadSmul b S), by
   simp only [AnomalyFreeQuadAddBMinusL, AnomalyFreeQuadSmul, HAdd.hAdd]
   simp only [Add.add]
   simp only [HSMul.hSMul]
   simp only [SMul.smul]
   rw [accCube_add, accCube_smul, accCube_smul, accCubeDiv_smul_left,
   accCubeDiv_smul_left, accCubeDiv_smul_right, accCubeDiv_smul_right]
   rw [BMinusL.Cube, hSSS, accCubeDiv_AnomalyFreeLinear_BMinusL, hB]
   simp only [mul_zero, add_zero]
  ⟩

@[simp]
def mapToCube : AnomalyFreeQuad × ℚ × ℚ → AnomalyFree :=  fun S =>
  if h : accCube S.1.val.val = 0 ∧ accCubeDiv BMinusL.val.val.val S.1.val.val = 0 then
    mapToCubeSpecial S.1 h.left h.right S.2.1 S.2.2
  else
    AnomalyFreeSMul S.2.1 (mapToCubeGeneric S.1)

theorem mapToCube_surjective : Function.Surjective mapToCube := by
  intro S
  by_cases hS :  accCube S.val.val.val = 0 ∧ accCubeDiv BMinusL.val.val.val S.val.val.val = 0
  · use ⟨S.val, ⟨0, 1⟩⟩
    rw [mapToCube]
    rw [dif_pos hS]
    rw [mapToCubeSpecial]
    apply AnomalyFree.ext
    simp [AnomalyFreeQuadAddBMinusL, AnomalyFreeQuadSmul]
  · use ⟨S.val, ⟨1/((-3 * accCubeDiv BMinusL.val.val.val S.val.val.val)), 0⟩⟩
    rw [mapToCube]
    rw [dif_neg hS]
    rw [mapToCubeGeneric_on_cube]
    rw [← AnomalyFree_mul_smul]
    rw [div_mul]
    rw [one_div_div]
    rw [div_self, AnomalyFree_one_smul]
    rw [S.Cube] at hS
    simp_all only [accCubeDiv, true_and, neg_mul, ne_eq, neg_eq_zero, _root_.mul_eq_zero,
      OfNat.ofNat_ne_zero, or_self, not_false_eq_true]

end QuadToCubic

end SMRHNPlusU1
