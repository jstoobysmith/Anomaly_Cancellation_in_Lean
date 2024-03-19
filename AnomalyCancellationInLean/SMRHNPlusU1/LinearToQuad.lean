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

namespace LinearToQuad

variable {n : ℕ}
variable (C : (SMRHNPlusU1 n).AnomalyFreeQuad)

@[simp]
def α₁ (S : (SMRHNPlusU1 n).AnomalyFreeLinear) : ℚ :=
  (- 2 * (accQuadBiLinear.toFun (C.val, S.val)))

@[simp]
def α₂ (S : (SMRHNPlusU1 n).AnomalyFreeLinear) : ℚ := (accQuad.toFun S.val)

def generic  (S : (SMRHNPlusU1 n).AnomalyFreeLinear) : (SMRHNPlusU1 n).AnomalyFreeQuad :=
  ⟨(α₂ S) • C.1 + (α₁ C S) • S
   , by
    intro i
    simp at i
    match i with
    | 0 =>
    erw [BiLinearSymm.toHomogeneousQuad_add]
    have hC := C.quadSol
    simp at hC
    erw [HomogeneousQuadratic.map_smul']
    erw [HomogeneousQuadratic.map_smul']
    erw [BiLinear.map_smul₁, BiLinear.map_smul₂]
    erw [hC 0]
    simp only [mul_zero, neg_mul, zero_add]
    rw [α₁, α₂]
    ring_nf
    simp⟩

lemma generic_on_AnomalyFreeQuad (S : (SMRHNPlusU1 n).AnomalyFreeQuad) :
    generic C S.1 = (α₁ C S.1) • S := by
  rw [generic]
  apply ACCSystemQuad.AnomalyFreeQuad.ext
  simp only
  rw [α₂]
  have hS := S.quadSol
  simp at hS
  erw [hS 0]
  simp
  rfl

def special (S : (SMRHNPlusU1 n).AnomalyFreeLinear) (h₁ : α₁ C S = 0)
    (h₂ : α₂ S = 0) (a b : ℚ) : (SMRHNPlusU1 n).AnomalyFreeQuad :=
  ⟨ a • C.1 + b • S, by
    intro i
    simp at i
    match i with
    | 0 =>
    erw [BiLinearSymm.toHomogeneousQuad_add]
    erw [HomogeneousQuadratic.map_smul', HomogeneousQuadratic.map_smul']
    have hC := C.quadSol
    simp at hC
    erw [hC 0]
    erw [BiLinear.map_smul₁, BiLinear.map_smul₂]
    simp_all
   ⟩

@[simp]
def linearToQuad  : (SMRHNPlusU1 n).AnomalyFreeLinear × ℚ × ℚ → (SMRHNPlusU1 n).AnomalyFreeQuad :=
  fun S =>
  if h : α₁ C S.1 = 0 ∧ α₂ S.1 = 0 then
    special C S.1 h.left h.right S.2.1 S.2.2
  else
    S.2.1 • (generic C S.1)

theorem linearToQuad_surjective : Function.Surjective (linearToQuad C) := by
  intro S
  by_cases hS :   α₁ C S.1 = 0 ∧ α₂ S.1 = 0
  · use ⟨S.1, ⟨0, 1⟩⟩
    rw [linearToQuad]
    rw [dif_pos hS]
    rw [special]
    apply ACCSystemQuad.AnomalyFreeQuad.ext
    simp only [zero_smul, one_smul, zero_add]
  · use ⟨S.1, ⟨1/(α₁ C S.1), 0⟩⟩
    rw [linearToQuad]
    rw [dif_neg hS]
    rw [generic_on_AnomalyFreeQuad]
    rw [← (SMRHNPlusU1 n).AnomalyFreeQuadMulAction.mul_smul]
    rw [div_mul]
    rw [one_div_div]
    rw [div_self, (SMRHNPlusU1 n).AnomalyFreeQuadMulAction.one_smul]
    have hS' := S.quadSol
    simp at hS'
    erw [α₂, hS' 0] at hS
    simp_all only [α₁, SMRHNPlusU1Charges_charges, accQuadBiLinear_toFun, neg_mul, neg_eq_zero,
      mul_eq_zero, OfNat.ofNat_ne_zero, false_or, and_true, ne_eq, or_self, not_false_eq_true]

end LinearToQuad

end SMRHNPlusU1
