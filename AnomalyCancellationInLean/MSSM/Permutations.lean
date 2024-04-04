/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.MSSM.Basic
import Mathlib.Tactic.Polyrith
import AnomalyCancellationInLean.GroupActions
universe v u

open Nat
open  Finset

namespace MSSM

open MSSMCharges
open MSSMACCs
open BigOperators

@[simp]
def permGroup := Fin 6 → Equiv.Perm (Fin 3)

@[simps!]
instance  : Group permGroup where
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
def chargeMap (f : permGroup) : MSSMCharges.charges →ₗ[ℚ] MSSMCharges.charges where
  toFun S := toSpecies.symm (fun i => toSMSpecies i S ∘ f i, Prod.snd (toSpecies S))
  map_add' S T := by
    simp only
    rw [charges_eq_toSpecies_eq]
    apply And.intro
    intro i
    rw [(toSMSpecies i).map_add]
    rw [toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv]
    simp only
    erw [(toSMSpecies i).map_add]
    rfl
    apply And.intro
    rw [Hd.map_add, Hd_toSpecies_inv, Hd_toSpecies_inv, Hd_toSpecies_inv]
    rfl
    rw [Hu.map_add, Hu_toSpecies_inv, Hu_toSpecies_inv, Hu_toSpecies_inv]
    rfl
  map_smul' a S := by
    simp only
    rw [charges_eq_toSpecies_eq]
    apply And.intro
    intro i
    rw [(toSMSpecies i).map_smul, toSMSpecies_toSpecies_inv, toSMSpecies_toSpecies_inv]
    rfl
    apply And.intro
    rfl
    rfl

lemma chargeMap_toSpecies (f : permGroup) (S : MSSMCharges.charges) (j : Fin 6) :
    toSMSpecies j (chargeMap f S) = toSMSpecies j S ∘ f j := by
  erw [toSMSpecies_toSpecies_inv]

@[simps!]
def repCharges : Representation ℚ (permGroup) (MSSMCharges).charges where
  toFun f := chargeMap f⁻¹
  map_mul' f g :=by
    simp only [permGroup, mul_inv_rev]
    apply LinearMap.ext
    intro S
    rw [charges_eq_toSpecies_eq]
    apply And.intro
    intro i
    simp only [ Pi.mul_apply, Pi.inv_apply, Equiv.Perm.coe_mul, LinearMap.mul_apply]
    rw [chargeMap_toSpecies, chargeMap_toSpecies]
    simp only [Pi.mul_apply, Pi.inv_apply]
    rw [chargeMap_toSpecies]
    rfl
    apply And.intro
    rfl
    rfl
  map_one' := by
    apply LinearMap.ext
    intro S
    rw [charges_eq_toSpecies_eq]
    apply And.intro
    intro i
    erw [toSMSpecies_toSpecies_inv]
    rfl
    apply And.intro
    rfl
    rfl

lemma repCharges_toSMSpecies (f : permGroup) (S : MSSMCharges.charges) (j : Fin 6) :
    toSMSpecies j (repCharges f S) = toSMSpecies j S ∘ f⁻¹ j := by
  erw [toSMSpecies_toSpecies_inv]

lemma toSpecies_sum_invariant (m : ℕ) (f : permGroup) (S : MSSMCharges.charges) (j : Fin 6) :
    ∑ i, ((fun a => a ^ m) ∘ toSMSpecies j (repCharges f S)) i =
    ∑ i, ((fun a => a ^ m) ∘ toSMSpecies j S) i := by
  erw [repCharges_toSMSpecies]
  change  ∑ i : Fin 3, ((fun a => a ^ m) ∘ _) (⇑(f⁻¹ _) i) = ∑ i : Fin 3, ((fun a => a ^ m) ∘ _) i
  refine Equiv.Perm.sum_comp _ _ _ ?_
  simp only [permGroup, Fin.isValue, Pi.inv_apply, ne_eq, coe_univ, Set.subset_univ]

lemma Hd_invariant (f : permGroup) (S : MSSMCharges.charges)  :
    Hd (repCharges f S) = Hd S := rfl

lemma Hu_invariant (f : permGroup) (S : MSSMCharges.charges)  :
    Hu (repCharges f S) = Hu S := rfl

lemma accGrav_invariant (f : permGroup) (S : MSSMCharges.charges)  :
    accGrav (repCharges f S) = accGrav S :=
  accGrav_ext
    (by simpa using toSpecies_sum_invariant 1 f S)
    (Hd_invariant f S)
    (Hu_invariant f S)

lemma accSU2_invariant (f : permGroup) (S : MSSMCharges.charges)  :
    accSU2 (repCharges f S) = accSU2 S :=
  accSU2_ext
    (by simpa using toSpecies_sum_invariant 1 f S)
    (Hd_invariant f S)
    (Hu_invariant f S)

lemma accSU3_invariant (f : permGroup) (S : MSSMCharges.charges)  :
    accSU3 (repCharges f S) = accSU3 S :=
  accSU3_ext
    (by simpa using toSpecies_sum_invariant 1 f S)

lemma accYY_invariant (f : permGroup) (S : MSSMCharges.charges)  :
    accYY (repCharges f S) = accYY S :=
  accYY_ext
    (by simpa using toSpecies_sum_invariant 1 f S)
    (Hd_invariant f S)
    (Hu_invariant f S)

lemma accQuad_invariant (f : permGroup) (S : MSSMCharges.charges)  :
    accQuad (repCharges f S) = accQuad S :=
  accQuad_ext
    (toSpecies_sum_invariant 2 f S)
    (Hd_invariant f S)
    (Hu_invariant f S)

lemma accCube_invariant (f : permGroup) (S : MSSMCharges.charges)  :
    accCube (repCharges f S) = accCube S :=
  accCube_ext
    (by simpa using toSpecies_sum_invariant 3 f S)
    (Hd_invariant f S)
    (Hu_invariant f S)




end MSSM
