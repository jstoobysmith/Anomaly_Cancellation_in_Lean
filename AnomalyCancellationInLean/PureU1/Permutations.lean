/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.PureU1.Basic
import Mathlib.Tactic.Polyrith
import Mathlib.RepresentationTheory.Basic
import Mathlib.Data.Fin.Tuple.Sort
import AnomalyCancellationInLean.GroupActions

universe v u

open Nat
open  Finset

namespace PureU1

@[simp]
def permGroup (n  : ℕ) := Equiv.Perm (Fin n)

instance {n : ℕ} : Group (permGroup n) := by
  simp [permGroup]
  infer_instance

section Charges
@[simps!]
def chargeMap {n : ℕ} (f : permGroup n) :
    (PureU1 n).charges  →ₗ[ℚ] (PureU1 n).charges where
  toFun S := S ∘ f.toFun
  map_add' S T := by
    funext i
    simp
  map_smul' a S := by
    funext i
    simp [HSMul.hSMul]
    rfl

open PureU1Charges in
@[simps!]
def permCharges {n : ℕ} : Representation ℚ (permGroup n) (PureU1 n).charges where
  toFun f := chargeMap f⁻¹
  map_mul' f g :=by
    simp
    apply LinearMap.ext
    intro S
    funext i
    rfl
  map_one' := by
    apply LinearMap.ext
    intro S
    funext i
    rfl

lemma accGrav_invariant {n : ℕ} (f : (permGroup n)) (S : (PureU1 n).charges) :
    PureU1.accGrav n (permCharges f S) = accGrav n S := by
  simp [accGrav, permCharges]
  apply (Equiv.Perm.sum_comp _ _ _ ?_)
  simp

open BigOperators
lemma accCube_invariant {n : ℕ} (f : (permGroup n)) (S : (PureU1 n).charges) :
    (accCube n).toFun (permCharges f S) = (accCube n).toFun S := by
  simp [accGrav, permCharges]
  change  ∑ i : Fin n, ((((fun a => a^3) ∘ S) (f.symm i))) = _
  apply (Equiv.Perm.sum_comp _ _ _ ?_)
  simp

end Charges

@[simps!]
def FamilyPermutations (n : ℕ) : ACCSystemGroupAction (PureU1 n) where
  group := permGroup n
  groupInst := inferInstance
  rep := permCharges
  linearInvariant := by
    intro i
    simp at i
    match i with
    | 0 => exact accGrav_invariant
  quadInvariant := by
    intro i
    simp at i
    exact Fin.elim0 i
  cubicInvariant := accCube_invariant


lemma FamilyPermutations_charges_apply (S : (PureU1 n).charges)
    (i : Fin n) (f : (FamilyPermutations n).group) :
    ((FamilyPermutations n).rep f S) i = S (f.invFun i) := by
  rfl


end PureU1
