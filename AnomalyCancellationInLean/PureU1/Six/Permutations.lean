/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.PureU1.Six.Basic
import Mathlib.Tactic.Polyrith
import Mathlib.RepresentationTheory.Basic

universe v u

open Nat
open  Finset

namespace PureU1
namespace Six

@[simp]
def permGroup := Equiv.Perm (Fin 6)

instance : Group permGroup := by
  simp [permGroup]
  infer_instance

@[simps!]
def chargeMap (f : Fin 6 → Fin 6) :
    Charges →ₗ[ℚ] Charges where
  toFun S := chargesMk (S.x ∘ f)
  map_add' S T := by
    apply Charges.ext <;>
      simp <;> split <;> rfl
  map_smul' a S := by
    apply Charges.ext <;>
      simp [chargesMk] <;> split <;> rfl

@[simps!]
def permCharges : Representation ℚ permGroup Charges where
  toFun f := chargeMap f.2
  map_mul' f g :=by
    apply LinearMap.ext
    intro S
    simp [chargeMap]
    rw [chargesMk_x]
    repeat rw [Function.comp.assoc]
    rfl
  map_one' := by
    simp [chargeMap]
    rfl

open BigOperators in
lemma accGrav_perm_inv (f : permGroup) (S : Charges) : accGrav (permCharges f S) = accGrav S := by
  rw [accGrav_eq_sum_univ, accGrav_eq_sum_univ]
  change  ∑ i : Fin 6, S.x (f.symm i) = _
  apply (Equiv.Perm.sum_comp _ _ _ ?_)
  simp

def anomalyFreeLinearMap (f : permGroup) : AnomalyFreeLinear →ₗ[ℚ] AnomalyFreeLinear where
  toFun S := ⟨permCharges f S.val, by rw [accGrav_perm_inv, S.Grav]⟩
  map_add' S T := by
    apply AnomalyFreeLinear.ext
    exact (chargeMap f.2).map_add' _ _
  map_smul' a S := by
    apply AnomalyFreeLinear.ext
    exact (chargeMap f.2).map_smul' _ _

@[simps!]
def permAnomalyFreeLinear : Representation ℚ permGroup AnomalyFreeLinear where
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
lemma accCube_perm_inv (f : permGroup) (S : Charges) : accCube (permCharges f S) = accCube S := by
  rw [accCube_eq_sum_univ, accCube_eq_sum_univ]
  change  ∑ i : Fin 6, ((((fun a => a^3) ∘ S.x) (f.symm i))) = _
  apply (Equiv.Perm.sum_comp _ _ _ ?_)
  simp

def permAnomalyFree : MulAction permGroup AnomalyFree where
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

end Six
end PureU1
