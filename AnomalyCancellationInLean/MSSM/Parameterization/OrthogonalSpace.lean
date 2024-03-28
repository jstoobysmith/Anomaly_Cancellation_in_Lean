/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.MSSM.Basic
import AnomalyCancellationInLean.MSSM.Parameterization.LineY3B3

import Mathlib.Tactic.Polyrith
-- Reference : https://arxiv.org/pdf/2107.07926.pdf

universe v u

namespace MSSMACC
open MSSMCharges
open MSSMACCs
open BigOperators

structure MSSMACC.AnomalyFreePerp extends MSSMACC.AnomalyFreeLinear where
  perpY₃ : dot (Y₃.val, val) = 0
  perpB₃ : dot (B₃.val, val) = 0

/-- The projection of an object in `MSSMACC.AnomalyFreeLinear` onto the subspace
  orthgonal to `Y₃` and`B₃`. -/
def proj (T : MSSMACC.AnomalyFreeLinear) : MSSMACC.AnomalyFreePerp :=
  ⟨(dot (B₃.val, T.val) - dot (Y₃.val, T.val)) • Y₃.1.1
  + (dot (Y₃.val, T.val) - 2 * dot (B₃.val, T.val)) • B₃.1.1
  + dot (Y₃.val, B₃.val) • T,
  by
    change dot (_, _ • Y₃.val + _ • B₃.val + _ • T.val) = 0
    rw [dot.map_add₂, dot.map_add₂]
    rw [dot.map_smul₂, dot.map_smul₂, dot.map_smul₂]
    rw [show dot (Y₃.val, B₃.val) = 108 by rfl]
    rw [show dot (Y₃.val, Y₃.val) = 216 by rfl]
    ring,
  by
    change dot (_, _ • Y₃.val + _ • B₃.val + _ • T.val) = 0
    rw [dot.map_add₂, dot.map_add₂]
    rw [dot.map_smul₂, dot.map_smul₂, dot.map_smul₂]
    rw [show dot (Y₃.val, B₃.val) = 108 by rfl]
    rw [show dot (B₃.val, Y₃.val) = 108 by rfl]
    rw [show dot (B₃.val, B₃.val) = 108 by rfl]
    ring⟩

lemma proj_val (T : MSSMACC.AnomalyFreeLinear) :
    (proj T).val = (dot (B₃.val, T.val) - dot (Y₃.val, T.val)) • Y₃.val +
    ( (dot (Y₃.val, T.val) - 2 * dot (B₃.val, T.val))) • B₃.val +
    dot (Y₃.val, B₃.val) • T.val := by
  rfl

lemma Y₃_plus_B₃_plus_proj (T : MSSMACC.AnomalyFreeLinear) (a b c : ℚ) :
    a • Y₃.val + b • B₃.val + c • (proj T).val =
    (a + c * (dot (B₃.val, T.val) - dot (Y₃.val, T.val))) • Y₃.val
    + (b + c * (dot (Y₃.val, T.val) - 2 * dot (B₃.val, T.val))) • B₃.val
    + (dot (Y₃.val, B₃.val) * c) • T.val:= by
  rw [proj_val]
  rw [DistribMulAction.smul_add, DistribMulAction.smul_add]
  rw [add_assoc (_ • _ • Y₃.val), ← add_assoc (_ • Y₃.val + _ • B₃.val), add_assoc (_ • Y₃.val)]
  rw [add_comm (_ • B₃.val) (_ • _ • Y₃.val), ← add_assoc (_ • Y₃.val)]
  rw [← MulAction.mul_smul, ← Module.add_smul]
  repeat rw [add_assoc]
  apply congrArg
  rw [← add_assoc, ← MulAction.mul_smul, ← Module.add_smul]
  apply congrArg
  simp
  rw [mul_comm, MulAction.mul_smul]



lemma quad_Y₃_proj (T : MSSMACC.AnomalyFreeLinear) :
    quadBiLin (Y₃.val, (proj T).val) = dot (Y₃.val, B₃.val) * quadBiLin (Y₃.val, T.val) := by
  rw [proj_val]
  rw [quadBiLin.map_add₂, quadBiLin.map_add₂]
  rw [quadBiLin.map_smul₂, quadBiLin.map_smul₂, quadBiLin.map_smul₂]
  rw [show quadBiLin (Y₃.val, B₃.val) = 0 by rfl]
  rw [show quadBiLin (Y₃.val, Y₃.val) = 0 by rfl]
  ring

lemma quad_B₃_proj (T : MSSMACC.AnomalyFreeLinear) :
    quadBiLin (B₃.val, (proj T).val) = dot (Y₃.val, B₃.val) * quadBiLin (B₃.val, T.val) := by
  rw [proj_val]
  rw [quadBiLin.map_add₂, quadBiLin.map_add₂]
  rw [quadBiLin.map_smul₂, quadBiLin.map_smul₂, quadBiLin.map_smul₂]
  rw [show quadBiLin (B₃.val, Y₃.val) = 0 by rfl]
  rw [show quadBiLin (B₃.val, B₃.val) = 0 by rfl]
  ring

lemma quad_self_proj (T : MSSMACC.AnomalyFree) :
    quadBiLin (T.val, (proj T.1.1).val) =
    (dot (B₃.val, T.val) - dot (Y₃.val, T.val)) * quadBiLin (Y₃.val, T.val) +
    (dot (Y₃.val, T.val) - 2 * dot (B₃.val, T.val)) * quadBiLin (B₃.val, T.val) := by
  rw [proj_val]
  rw [quadBiLin.map_add₂, quadBiLin.map_add₂]
  rw [quadBiLin.map_smul₂, quadBiLin.map_smul₂, quadBiLin.map_smul₂]
  erw [quadSol T.1]
  rw [quadBiLin.swap T.val Y₃.val, quadBiLin.swap T.val B₃.val]
  ring

lemma quad_proj (T : MSSMACC.AnomalyFree) :
    quadBiLin ((proj T.1.1).val, (proj T.1.1).val) = 2 * (dot (Y₃.val, B₃.val)) *
     ((dot (B₃.val, T.val) - dot (Y₃.val, T.val)) * quadBiLin (Y₃.val, T.val) +
   (dot (Y₃.val, T.val) - 2 * dot (B₃.val, T.val)) * quadBiLin (B₃.val, T.val) ) := by
  nth_rewrite 1 [proj_val]
  repeat rw [quadBiLin.map_add₁]
  repeat rw [quadBiLin.map_smul₁]
  rw [quad_Y₃_proj, quad_B₃_proj, quad_self_proj]
  ring


lemma cube_proj_proj_Y₃ (T : MSSMACC.AnomalyFreeLinear) :
    cubeTriLin ((proj T).val, (proj T).val, Y₃.val) =
    (dot (Y₃.val, B₃.val))^2 * cubeTriLin (T.val, T.val, Y₃.val):= by
  rw [proj_val]
  rw [cubeTriLin.map_add₁, cubeTriLin.map_add₂]
  erw [lineY₃B₃_doublePoint]
  rw [cubeTriLin.map_add₂]
  rw [cubeTriLin.swap₂]
  rw [cubeTriLin.map_add₁, cubeTriLin.map_smul₁, cubeTriLin.map_smul₃]
  rw [doublePoint_Y₃_Y₃]
  rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₃, cubeTriLin.swap₁]
  rw [doublePoint_Y₃_B₃]
  rw [cubeTriLin.map_add₂]
  rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₂]
  rw [cubeTriLin.swap₁, cubeTriLin.swap₂]
  rw [doublePoint_Y₃_Y₃]
  rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₂]
  rw [cubeTriLin.swap₁, cubeTriLin.swap₂, cubeTriLin.swap₁]
  rw [doublePoint_Y₃_B₃]
  rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₂]
  ring

lemma cube_proj_proj_B₃ (T : MSSMACC.AnomalyFreeLinear) :
    cubeTriLin ((proj T).val, (proj T).val, B₃.val) =
    (dot (Y₃.val, B₃.val))^2 * cubeTriLin (T.val, T.val, B₃.val):= by
  rw [proj_val]
  rw [cubeTriLin.map_add₁, cubeTriLin.map_add₂]
  erw [lineY₃B₃_doublePoint]
  rw [cubeTriLin.map_add₂, cubeTriLin.swap₂, cubeTriLin.map_add₁, cubeTriLin.map_smul₁,
    cubeTriLin.map_smul₃, doublePoint_Y₃_B₃]
  rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₃, cubeTriLin.swap₁, doublePoint_B₃_B₃]
  rw [cubeTriLin.map_add₂, cubeTriLin.map_smul₁, cubeTriLin.map_smul₂]
  rw [cubeTriLin.swap₁, cubeTriLin.swap₂, doublePoint_Y₃_B₃]
  rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₂, cubeTriLin.swap₁, cubeTriLin.swap₂,
   cubeTriLin.swap₁, doublePoint_B₃_B₃]
  rw [cubeTriLin.map_smul₁, cubeTriLin.map_smul₂]
  ring

lemma cube_proj_proj_self (T : MSSMACC.AnomalyFree) :
    cubeTriLin ((proj T.1.1).val, (proj T.1.1).val, T.val) =
    2 * dot (Y₃.val, B₃.val) *
    ((dot (B₃.val, T.val) - dot (Y₃.val, T.val)) * cubeTriLin (T.val, T.val, Y₃.val)  +
    ( dot (Y₃.val, T.val)- 2 * dot (B₃.val, T.val)) * cubeTriLin (T.val, T.val, B₃.val)) := by
  rw [proj_val]
  rw [cubeTriLin.map_add₁, cubeTriLin.map_add₂]
  erw [lineY₃B₃_doublePoint]
  repeat rw [cubeTriLin.map_add₁]
  repeat rw [cubeTriLin.map_smul₁]
  repeat rw [cubeTriLin.map_add₂]
  repeat rw [cubeTriLin.map_smul₂]
  erw [T.cubicSol]
  rw [cubeTriLin.swap₁ Y₃.val T.val T.val, cubeTriLin.swap₂ T.val  Y₃.val T.val]
  rw [cubeTriLin.swap₁ B₃.val T.val T.val, cubeTriLin.swap₂ T.val  B₃.val T.val]
  ring

lemma cube_proj (T : MSSMACC.AnomalyFree) :
    cubeTriLin ((proj T.1.1).val, (proj T.1.1).val, (proj T.1.1).val) =
    3 *  dot (Y₃.val, B₃.val) ^ 2 *
    ((dot (B₃.val, T.val) - dot (Y₃.val, T.val)) * cubeTriLin (T.val, T.val, Y₃.val) +
        (dot (Y₃.val, T.val) - 2 * dot (B₃.val, T.val)) * cubeTriLin (T.val, T.val, B₃.val)) := by
  nth_rewrite 3 [proj_val]
  repeat rw [cubeTriLin.map_add₃]
  repeat rw [cubeTriLin.map_smul₃]
  rw [cube_proj_proj_Y₃, cube_proj_proj_B₃, cube_proj_proj_self]
  ring



end MSSMACC
