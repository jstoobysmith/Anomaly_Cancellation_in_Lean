/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.PureU1.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.BigOperators.Fin
universe v u

open Nat
open  Finset

namespace PureU1
namespace Six

section Charges

structure Charges where
  x1 : ℚ
  x2 : ℚ
  x3 : ℚ
  x4 : ℚ
  x5 : ℚ
  x6 : ℚ

@[ext]
lemma Charges.ext {S T : Charges}
    (h1 : S.x1 = T.x1) (h2 : S.x2 = T.x2) (h3 : S.x3 = T.x3) (h4 : S.x4 = T.x4)
    (h5 : S.x5 = T.x5) (h6 : S.x6 = T.x6) : S = T := by
  cases' S
  simp_all only

@[simps!]
instance chargesAddCommMonoid : AddCommMonoid Charges where
  add S T :=
    ⟨S.x1 + T.x1, S.x2 + T.x2, S.x3 + T.x3, S.x4 + T.x4, S.x5 + T.x5, S.x6 + T.x6⟩
  add_assoc S T L := by
    apply Charges.ext <;> exact Rat.add_assoc _ _ _
  zero :=
    ⟨0, 0, 0, 0, 0, 0⟩
  zero_add S := by
    apply Charges.ext <;> exact Rat.zero_add _
  add_zero S := by
    apply Charges.ext <;> exact Rat.add_zero _
  add_comm S T:= by
    apply Charges.ext <;> exact Rat.add_comm _ _

@[simp]
def Charges.x (S : Charges) : Fin 6 → ℚ := fun a =>
  match a with
  | 0 => S.x1
  | 1 => S.x2
  | 2 => S.x3
  | 3 => S.x4
  | 4 => S.x5
  | 5 => S.x6


@[simps!]
def chargesMk (f : Fin 6 → ℚ) : Charges :=
  ⟨f 0, f 1, f 2, f 3, f 4, f 5⟩

lemma chargesMk_x (f : Fin 6 → ℚ) : (chargesMk f).x = f := by
  funext a
  simp
  split <;> rfl


@[simps!]
instance chargesModule : Module ℚ Charges where
  smul a S :=
    ⟨a * S.x1, a * S.x2, a * S.x3, a * S.x4, a * S.x5, a * S.x6⟩
  one_smul one_smul := by
    apply Charges.ext <;> exact Rat.one_mul _
  mul_smul a b S := by
    apply Charges.ext <;> exact Rat.mul_assoc _ _ _
  smul_zero a := by
    apply Charges.ext <;> exact Rat.mul_zero _
  zero_smul S := by
    apply Charges.ext <;> exact Rat.zero_mul _
  smul_add a S T := by
    apply Charges.ext <;> exact Rat.mul_add _ _ _
  add_smul a b T:= by
    apply Charges.ext <;> exact Rat.add_mul _ _ _

end Charges

section LinearACCs

@[simps!]
def accGrav : Charges →ₗ[ℚ] ℚ where
  toFun S := S.x1 + S.x2 + S.x3 + S.x4 + S.x5 + S.x6
  map_add' S T := by
    simp
    ring
  map_smul' a S := by
    simp
    simp [HSMul.hSMul]
    rw [show @Rat.cast ℚ DivisionRing.toRatCast a = a from rfl]
    ring


open BigOperators in
lemma accGrav_eq_sum_univ (S : Charges) : accGrav S = ∑ i : Fin 6, S.x i :=
   (Fin.sum_univ_six fun i => S.x i).symm


structure AnomalyFreeLinear where
  val : Charges
  Grav : accGrav val = 0

@[ext]
lemma AnomalyFreeLinear.ext {S T : AnomalyFreeLinear} (h : S.val = T.val) : S = T := by
  cases' S
  simp_all only

instance AnomalyFreeLinearAddCommMonoid : AddCommMonoid AnomalyFreeLinear where
  add S T := ⟨S.val + T.val, by rw [accGrav.map_add, S.Grav, T.Grav]; simp⟩
  add_comm S T := by
    apply AnomalyFreeLinear.ext
    exact chargesAddCommMonoid.add_comm _ _
  add_assoc S T L := by
    apply AnomalyFreeLinear.ext
    exact chargesAddCommMonoid.add_assoc _ _ _
  zero := ⟨chargesAddCommMonoid.zero, by rfl⟩
  zero_add S := by
    apply AnomalyFreeLinear.ext
    exact chargesAddCommMonoid.zero_add _
  add_zero S := by
    apply AnomalyFreeLinear.ext
    exact chargesAddCommMonoid.add_zero _

instance AnomalyFreeLinearAddCommModule : Module ℚ AnomalyFreeLinear where
  smul a S := ⟨a • S.val, by rw [accGrav.map_smul, S.Grav]; simp⟩
  one_smul one_smul := by
    apply AnomalyFreeLinear.ext
    exact chargesModule.one_smul _
  mul_smul a b S := by
    apply AnomalyFreeLinear.ext
    exact chargesModule.mul_smul _ _ _
  smul_zero a := by
    apply AnomalyFreeLinear.ext
    exact chargesModule.smul_zero _
  zero_smul S := by
    apply AnomalyFreeLinear.ext
    exact chargesModule.zero_smul _
  smul_add a S T := by
    apply AnomalyFreeLinear.ext
    exact chargesModule.smul_add _ _ _
  add_smul a b T:= by
    apply AnomalyFreeLinear.ext
    exact chargesModule.add_smul _ _ _

end LinearACCs

@[simps!]
instance cubeAction : MulAction ℚ ℚ where
  smul a b := a^3 * b
  mul_smul a b c:= by
   simp [HSMul.hSMul]
   ring
  one_smul a := by
   simp [HSMul.hSMul]

@[simps!]
instance cubeActionSMUL : SMul ℚ ℚ := cubeAction.toSMul

def accCube : @MulActionHom ℚ Charges _ ℚ cubeActionSMUL where
  toFun S := S.x1^3 + S.x2^3 + S.x3^3 + S.x4^3 + S.x5^3 + S.x6^3
  map_smul' a S := by
    simp [HSMul.hSMul, SMul.smul]
    ring

open BigOperators in
lemma accCube_eq_sum_univ (S : Charges) : accCube S = ∑ i : Fin 6, ((fun a => a^3) ∘ S.x) i :=
  (Fin.sum_univ_six fun i => ((fun a => a^3) ∘ S.x) i).symm

structure AnomalyFree where
  val : AnomalyFreeLinear
  Cube : accCube val.val = 0

@[ext]
lemma AnomalyFree.ext {S T : AnomalyFree} (h : S.val.val = T.val.val) : S = T := by
  have h1 : S.val = T.val := AnomalyFreeLinear.ext h
  cases' S
  simp_all

/-- The scalar multiple of any solution is also a solution. -/
instance AnomalyFreeMulAction : MulAction ℚ AnomalyFree where
  smul a S :=  ⟨ a • S.val,
    by erw [accCube.map_smul, S.Cube]; simp⟩
  mul_smul a b S := by
    apply AnomalyFree.ext
    exact mul_smul _ _ _
  one_smul S := by
    apply AnomalyFree.ext
    exact one_smul _ _

@[simps!]
def Γ₁ (k1 k2 k3 : ℚ) : Charges where
  x1 := k1
  x2 := k2
  x3 := k3
  x4 := - k1
  x5 := - k2
  x6 := - k3

@[simps!]
def Γ₂ (l1 l2 : ℚ) : Charges where
  x1 := 0
  x2 := l1
  x3 := l2
  x4 := - l1
  x5 := - l2
  x6 := 0

lemma Γ₁_Γ₂_disjoint (k1 k2 k3 l1 l2 : ℚ) (h : Γ₁ k1 k2 k3 = Γ₂ l1 l2) :
    k1 = 0 ∧ k2 = 0 ∧ k3 = 0 ∧ l1 = 0 ∧ l2 = 0 := by
  simp [Γ₁, Γ₂] at h
  have hl := h.left
  subst hl
  simp_all
  have hl := h.left
  subst hl
  simp_all



end Six
end PureU1
