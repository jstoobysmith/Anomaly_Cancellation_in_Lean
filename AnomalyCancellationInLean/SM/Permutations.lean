/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.SM.Basic
import Mathlib.Tactic.Polyrith
import AnomalyCancellationInLean.GroupActions
/-!
# Permutations of SM with no RHN.

We define the group of permutations for the SM charges with no RHN.

-/

universe v u

open Nat
open  Finset

namespace SM

open SMCharges
open SMACCs
open BigOperators

@[simp]
def permGroup (n : ℕ) := Fin 5 → Equiv.Perm (Fin n)

variable {n : ℕ}

@[simps!]
instance : Group (permGroup n) where
  mul f g := fun i => f i * g i
  mul_assoc f g h := by
    funext i
    simp_all only [permGroup, Pi.mul_apply]
    rfl
  one := fun _ => 1
  one_mul f := by
    funext i
    simp_all only [permGroup, Pi.mul_apply]
    rfl
  mul_one f := by
    funext i
    simp_all only [permGroup, Pi.mul_apply]
    rfl
  inv f := fun i => (f i)⁻¹
  mul_left_inv f := by
    funext i
    simp_all only [permGroup, Pi.mul_apply]
    simp_all only [mul_left_inv, Pi.one_apply]

@[simps!]
def chargeMap (f : permGroup n) : (SMCharges n).charges →ₗ[ℚ] (SMCharges n).charges where
  toFun S := toSpeciesEquiv.symm (fun i => toSpecies i S ∘ f i )
  map_add' S T := by
    simp only
    rw [charges_eq_toSpecies_eq]
    intro i
    rw [(toSpecies i).map_add]
    rw [toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv]
    rfl
  map_smul' a S := by
    simp only
    rw [charges_eq_toSpecies_eq]
    intro i
    rw [(toSpecies i).map_smul, toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv]
    rfl

@[simps!]
def repCharges {n : ℕ} : Representation ℚ (permGroup n) (SMCharges n).charges where
  toFun f := chargeMap f⁻¹
  map_mul' f g :=by
    simp only [permGroup, mul_inv_rev]
    apply LinearMap.ext
    intro S
    rw [charges_eq_toSpecies_eq]
    intro i
    simp only [chargeMap_apply, Pi.mul_apply, Pi.inv_apply, Equiv.Perm.coe_mul, LinearMap.mul_apply]
    repeat erw [toSMSpecies_toSpecies_inv]
    rfl
  map_one' := by
    apply LinearMap.ext
    intro S
    rw [charges_eq_toSpecies_eq]
    intro i
    erw [toSMSpecies_toSpecies_inv]
    rfl

lemma repCharges_toSpecies (f : permGroup n) (S : (SMCharges n).charges) (j : Fin 5) :
    toSpecies j (repCharges f S) = toSpecies j S ∘ f⁻¹ j := by
  erw [toSMSpecies_toSpecies_inv]


lemma toSpecies_sum_invariant (m : ℕ) (f : permGroup n) (S : (SMCharges n).charges) (j : Fin 5) :
    ∑ i, ((fun a => a ^ m) ∘ toSpecies j (repCharges f S)) i =
    ∑ i, ((fun a => a ^ m) ∘ toSpecies j S) i := by
  erw [repCharges_toSpecies]
  change  ∑ i : Fin n, ((fun a => a ^ m) ∘ _) (⇑(f⁻¹ _) i) = ∑ i : Fin n, ((fun a => a ^ m) ∘ _) i
  refine Equiv.Perm.sum_comp _ _ _ ?_
  simp only [permGroup, Fin.isValue, Pi.inv_apply, ne_eq, coe_univ, Set.subset_univ]


lemma accGrav_invariant (f : permGroup n) (S : (SMCharges n).charges)  :
    accGrav (repCharges f S) = accGrav S :=
  accGrav_ext
    (by simpa using toSpecies_sum_invariant 1 f S)


lemma accSU2_invariant (f : permGroup n) (S : (SMCharges n).charges)  :
    accSU2 (repCharges f S) = accSU2 S :=
  accSU2_ext
    (by simpa using toSpecies_sum_invariant 1 f S)


lemma accSU3_invariant (f : permGroup n) (S : (SMCharges n).charges)  :
    accSU3 (repCharges f S) = accSU3 S :=
  accSU3_ext
    (by simpa using toSpecies_sum_invariant 1 f S)

lemma accYY_invariant (f : permGroup n) (S : (SMCharges n).charges)  :
    accYY (repCharges f S) = accYY S :=
  accYY_ext
    (by simpa using toSpecies_sum_invariant 1 f S)

lemma accQuad_invariant (f : permGroup n) (S : (SMCharges n).charges)  :
    accQuad (repCharges f S) = accQuad S :=
  accQuad_ext
    (toSpecies_sum_invariant 2 f S)

lemma accCube_invariant (f : permGroup n) (S : (SMCharges n).charges)  :
    accCube (repCharges f S) = accCube S :=
  accCube_ext
    (by simpa using toSpecies_sum_invariant 3 f S)

end SM
