/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.PureU1.Basic
import Mathlib.Tactic.Polyrith
import Mathlib.RepresentationTheory.Basic

universe v u

open Nat
open  Finset

namespace PureU1

@[simp]
def permGroup (n  : ℕ ) := Equiv.Perm (Fin n)

instance {n : ℕ} : Group (permGroup n) := by
  simp [permGroup]
  infer_instance

section Charges
@[simps!]
def chargeMap {n : ℕ} (f : Fin n → Fin n) :
    Charges n →ₗ[ℚ] Charges n where
  toFun S := ⟨S.x ∘ f⟩
  map_add' S T := by
    apply Charges.ext
    simp
  map_smul' a S := by
    apply Charges.ext
    intro i
    simp [HSMul.hSMul]
    apply Or.inl
    rfl

@[simps!]
def permCharges {n : ℕ} : Representation ℚ (permGroup n) (Charges n) where
  toFun f := chargeMap f.2
  map_mul' f g :=by
    apply LinearMap.ext
    intro S
    simp [chargeMap]
    repeat rw [Function.comp.assoc]
    rfl
  map_one' := by
    simp [chargeMap]
    rfl
end Charges

section Linear

open BigOperators in
lemma accGrav_perm_inv {n : ℕ} (f : permGroup n) (S : Charges n) :
    accGrav (permCharges f S) = accGrav S := by
  simp [accGrav, permCharges]
  apply (Equiv.Perm.sum_comp _ _ _ ?_)
  simp

def anomalyFreeLinearMap {n : ℕ} (f : permGroup n) :
    AnomalyFreeLinear n →ₗ[ℚ] AnomalyFreeLinear n where
  toFun S := ⟨permCharges f S.val, by rw [accGrav_perm_inv, S.Grav]⟩
  map_add' S T := by
    apply AnomalyFreeLinear.ext
    exact (chargeMap f.2).map_add' _ _
  map_smul' a S := by
    apply AnomalyFreeLinear.ext
    exact (chargeMap f.2).map_smul' _ _

@[simps!]
def permAnomalyFreeLinear {n : ℕ} : Representation ℚ (permGroup n) (AnomalyFreeLinear n) where
  toFun f := anomalyFreeLinearMap f
  map_mul' f g := by
    apply LinearMap.ext
    intro S
    apply AnomalyFreeLinear.ext
    change (permCharges.toFun (f * g)) S.val = _
    rw [permCharges.map_mul']
    rfl
  map_one' := by
    apply LinearMap.ext
    intro S
    apply AnomalyFreeLinear.ext
    change (permCharges.toFun 1) S.val = _
    rw [permCharges.map_one']
    rfl


open BigOperators in
lemma accCube_perm_inv {n : ℕ} (f : permGroup n) (S : Charges n) : accCube (permCharges f S) = accCube S := by
  simp [accGrav, permCharges]
  change  ∑ i : Fin n, ((((fun a => a^3) ∘ S.x) (f.symm i))) = _
  apply (Equiv.Perm.sum_comp _ _ _ ?_)
  simp

/-- The group action of the permutation group on the solutions to the
 anomaly free equations. -/
def permAnomalyFree {n : ℕ} : MulAction (permGroup n) (AnomalyFree n) where
  smul f S := ⟨permAnomalyFreeLinear f S.val, by
    change accCube (permCharges f S.val.val) = _
    rw [accCube_perm_inv, S.Cube]
  ⟩
  mul_smul f1 f2 S := by
    apply AnomalyFree.ext
    change (permCharges.toFun (f1 * f2)) S.val.val = _
    rw [permCharges.map_mul']
    rfl
  one_smul S := by
    apply AnomalyFree.ext
    change (permCharges.toFun 1) S.val.val = _
    rw [permCharges.map_one']
    rfl

end Linear
end PureU1
