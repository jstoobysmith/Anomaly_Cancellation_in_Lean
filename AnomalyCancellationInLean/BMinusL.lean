/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.Basics

@[simps!]
def oneFamilyBMinusL : oneFamilyCharge := ⟨1, -1, -1, -3, 3, 3⟩

@[simps!]
def BMinusL : AnomalyFree :=
  ⟨⟨⟨oneFamilyToThreeFamily oneFamilyBMinusL, by rfl, by rfl, by rfl, by rfl⟩, by rfl⟩, by rfl⟩

@[simp]
lemma accQuadDiv_BMinusL (S : threeFamilyCharge) :
    accQuadDiv BMinusL.val.val.val S = 1/2 * accYY S + 3/2 * accSU2 S - 2 * accSU3 S := by
  simp [BMinusL, oneFamilyBMinusL]
  ring

@[simp]
def AnomalyFreeQuadAddBMinusL (a : ℚ) (S : AnomalyFreeQuad) : AnomalyFreeQuad :=
   ⟨S.val + a • BMinusL.val.val,
    by
      erw [accQuad_add, S.Quad, accQuad_smul, BMinusL.val.Quad, accQuadDiv_smul_right,
      accQuadDiv_BMinusL, S.val.YY, S.val.SU3, S.val.SU2]
      simp only [one_div, mul_zero, add_zero, sub_self]⟩

def AnomalyFreeQuadAddBMinusL_zero (S : AnomalyFreeQuad) : AnomalyFreeQuadAddBMinusL 0 S = S := by
  simp only [AnomalyFreeQuadAddBMinusL, zero_smul, add_zero]


@[simp]
lemma accQuadDiv_BMinusL_AnomalyFreeLinear (S : AnomalyFreeLinear) :
    accQuadDiv BMinusL.val.val.val S.val = 0 := by
  rw [accQuadDiv_BMinusL]
  rw [S.YY, S.SU2, S.SU3]
  rfl

@[simp]
lemma accCubeDiv_of_BMinusL (S : threeFamilyCharge) :
    accCubeDiv S BMinusL.val.val.val = 9 * accGrav S - 24 * accSU3 S := by
  simp [BMinusL, oneFamilyBMinusL]
  ring

@[simp]
lemma accCubeDiv_AnomalyFreeLinear_BMinusL (S : AnomalyFreeLinear) :
    accCubeDiv S.val BMinusL.val.val.val = 0 := by
  rw [accCubeDiv_of_BMinusL]
  rw [S.Grav, S.SU3]
  rfl
