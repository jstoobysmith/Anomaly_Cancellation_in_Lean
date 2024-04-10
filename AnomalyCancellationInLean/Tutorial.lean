/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Tactic.Polyrith
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic.Polyrith

/-- The type of three family charges for pure U(1). -/
def three : Type := Fin 3 → ℚ

/-- The gravitational anomaly cancellation condition. -/
@[simp]
def accGrav (S : three) : ℚ := S 0 + S 1 + S 2

/-- The cubic anomaly cancellation condition. -/
@[simp]
def accCube (S : three) : ℚ := S 0 ^ 3 + S 1 ^ 3 + S 2 ^ 3

/-- The type of solutions to the gravitational anomaly cancellation condition. -/
structure LinSols where
  val : three
  grav : accGrav val = 0

/-- The type of solutions to all the anomaly cancellation conditions. -/
structure Sols extends LinSols where
  cube : accCube val = 0

/-- A specific example of a solution. -/
def vectorLike : Sols := ⟨⟨
  fun i => match i with
  | 0 => 1
  | 1 => -1
  | 2 => 0,
  by rfl⟩, by rfl⟩

/-- An equivalence between `ℚ²` and the linear solutions. -/
@[simps!]
def equiv : (Fin 2 → ℚ) ≃ LinSols where
  toFun := fun f => ⟨fun i => match i with
    | 0 => f 0
    | 1 => f 1
    | 2 => - f 0 - f 1, by simp⟩
  invFun := fun S => fun i => match i with
    | 0 => S.val 0
    | 1 => S.val 1
  left_inv f := by
    funext i
    match i with
    | 0 => rfl
    | 1 => rfl
  right_inv S := by
    cases' S with S grav
    simp
    funext i
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 =>
      simp
      simp at grav
      linear_combination - grav

/-- A charge is a solution only if one if its entries is zeros. -/
theorem sol_iff_one_zero (S : Sols) : S.val 0 = 0 ∨ S.val 1 = 0 ∨ S.val 2 = 0 := by
  let f := equiv.symm S.1
  have hC := S.cube
  simp at hC
  have ht : S.val = (equiv f).val := by
    aesop
  rw [ht] at hC
  rw [ht]
  simp only [Fin.isValue, equiv_apply_val]
  simp at hC
  have h : f 0 ^ 3 + f 1 ^ 3 + (-f 0 - f 1) ^ 3 = - 3 * f 0 * f 1 * (f 0 + f 1) := by
    ring_nf
  rw [h] at hC
  simp at hC
  cases' hC <;> rename_i hC
  cases' hC <;> rename_i hC
  rw [hC]
  simp
  rw [hC]
  simp only [Fin.isValue, sub_zero, neg_eq_zero, true_or, or_true]
  apply Or.inr
  apply Or.inr
  rw [@add_eq_zero_iff_neg_eq] at hC
  rw [← hC]
  simp only [Fin.isValue, sub_self]
