/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.SMRHNPlusU1.Basic
import Mathlib.Tactic.Polyrith
import AnomalyCancellationInLean.GroupActions
universe v u

open Nat
open  Finset

namespace SMRHNPlusU1

@[simp]
def permGroup (n : ℕ) := Fin 6 → Equiv.Perm (Fin n)

@[simps!]
instance {n : ℕ} : Group (permGroup n) where
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



section Charges
open SMRHNPlusU1Charges in
@[simps!]
def chargeMap {n : ℕ} (f : permGroup n) :
    (SMRHNPlusU1 n).charges  →ₗ[ℚ] (SMRHNPlusU1 n).charges where
  toFun S := SMRHNPlusU1Charges.mkFromSpecies (Q.toFun S ∘ f 0) (U.toFun S ∘ f 1)
    (D.toFun S ∘ f 2) (L.toFun S ∘ f 3) (E.toFun S ∘ f 4) (N.toFun S ∘ f 5)
  map_add' S T := by
    apply SMRHNPlusU1Charges.ext
    rw [Q.map_add']
    repeat rw [mkFromSpecies_Q]
    rfl
    rw [U.map_add']
    repeat rw [mkFromSpecies_U]
    rfl
    rw [D.map_add']
    repeat rw [mkFromSpecies_D]
    rfl
    rw [L.map_add']
    repeat rw [mkFromSpecies_L]
    rfl
    rw [E.map_add']
    repeat rw [mkFromSpecies_E]
    rfl
    rw [N.map_add']
    repeat rw [mkFromSpecies_N]
    rfl
  map_smul' a S := by
    apply SMRHNPlusU1Charges.ext
    rw [Q.map_smul']
    repeat rw [mkFromSpecies_Q]
    rfl
    rw [U.map_smul']
    repeat rw [mkFromSpecies_U]
    rfl
    rw [D.map_smul']
    repeat rw [mkFromSpecies_D]
    rfl
    rw [L.map_smul']
    repeat rw [mkFromSpecies_L]
    rfl
    rw [E.map_smul']
    repeat rw [mkFromSpecies_E]
    rfl
    rw [N.map_smul']
    repeat rw [mkFromSpecies_N]
    rfl

open SMRHNPlusU1Charges in
@[simps!]
def permCharges {n : ℕ} : Representation ℚ (permGroup n) (SMRHNPlusU1 n).charges where
  toFun f := chargeMap f⁻¹
  map_mul' f g :=by
    simp
    apply LinearMap.ext
    intro S
    apply SMRHNPlusU1Charges.ext
    repeat erw [mkFromSpecies_Q]
    rfl
    repeat erw [mkFromSpecies_U]
    rfl
    repeat erw [mkFromSpecies_D]
    rfl
    repeat erw [mkFromSpecies_L]
    rfl
    repeat erw [mkFromSpecies_E]
    rfl
    repeat erw [mkFromSpecies_N]
    rfl
  map_one' := by
    apply LinearMap.ext
    intro S
    apply SMRHNPlusU1Charges.ext
    erw [mkFromSpecies_Q]
    rfl
    erw [mkFromSpecies_U]
    rfl
    erw [mkFromSpecies_D]
    rfl
    erw [mkFromSpecies_L]
    rfl
    erw [mkFromSpecies_E]
    rfl
    erw [mkFromSpecies_N]
    rfl

end Charges

section invariantSums
open BigOperators
open SMRHNPlusU1Charges

lemma Q_pow_sum_invariant {n : ℕ} (m : ℕ) (f : (permGroup n)) (S : (SMRHNPlusU1 n).charges) :
    ∑ i, ((fun a => a^m) ∘ Q.toFun (permCharges f S)) i= ∑ i, ((fun a => a^m) ∘ Q.toFun S) i := by
  erw [mkFromSpecies_Q]
  change  ∑ i : Fin n, ((fun a => a ^ m) ∘ _) (⇑(f⁻¹ _) i) = ∑ i : Fin n, ((fun a => a ^ m) ∘ _) i
  refine Equiv.Perm.sum_comp _ _ _ ?_
  simp only [permGroup, Fin.isValue, Pi.inv_apply, ne_eq, coe_univ, Set.subset_univ]

lemma U_pow_sum_invariant {n : ℕ} (m : ℕ) (f : (permGroup n)) (S : (SMRHNPlusU1 n).charges) :
    ∑ i, ((fun a => a^m) ∘ U.toFun (permCharges f S)) i= ∑ i, ((fun a => a^m) ∘ U.toFun S) i := by
  erw [mkFromSpecies_U]
  change  ∑ i : Fin n, ((fun a => a ^ m) ∘ _) (⇑(f⁻¹ _) i) = ∑ i : Fin n, ((fun a => a ^ m) ∘ _) i
  refine Equiv.Perm.sum_comp _ _ _ ?_
  simp only [permGroup, Fin.isValue, Pi.inv_apply, ne_eq, coe_univ, Set.subset_univ]

lemma D_pow_sum_invariant {n : ℕ} (m : ℕ) (f : (permGroup n)) (S : (SMRHNPlusU1 n).charges) :
    ∑ i, ((fun a => a^m) ∘ D.toFun (permCharges f S)) i= ∑ i, ((fun a => a^m) ∘ D.toFun S) i := by
  erw [mkFromSpecies_D]
  change  ∑ i : Fin n, ((fun a => a ^ m) ∘ _) (⇑(f⁻¹ _) i) = ∑ i : Fin n, ((fun a => a ^ m) ∘ _) i
  refine Equiv.Perm.sum_comp _ _ _ ?_
  simp only [permGroup, Fin.isValue, Pi.inv_apply, ne_eq, coe_univ, Set.subset_univ]

lemma L_pow_sum_invariant {n : ℕ} (m : ℕ) (f : (permGroup n)) (S : (SMRHNPlusU1 n).charges) :
    ∑ i, ((fun a => a^m) ∘ L.toFun (permCharges f S)) i= ∑ i, ((fun a => a^m) ∘ L.toFun S) i := by
  erw [mkFromSpecies_L]
  change  ∑ i : Fin n, ((fun a => a ^ m) ∘ _) (⇑(f⁻¹ _) i) = ∑ i : Fin n, ((fun a => a ^ m) ∘ _) i
  refine Equiv.Perm.sum_comp _ _ _ ?_
  simp only [permGroup, Fin.isValue, Pi.inv_apply, ne_eq, coe_univ, Set.subset_univ]

lemma E_pow_sum_invariant {n : ℕ} (m : ℕ) (f : (permGroup n)) (S : (SMRHNPlusU1 n).charges) :
    ∑ i, ((fun a => a^m) ∘ E.toFun (permCharges f S)) i= ∑ i, ((fun a => a^m) ∘ E.toFun S) i := by
  erw [mkFromSpecies_E]
  change  ∑ i : Fin n, ((fun a => a ^ m) ∘ _) (⇑(f⁻¹ _) i) = ∑ i : Fin n, ((fun a => a ^ m) ∘ _) i
  refine Equiv.Perm.sum_comp _ _ _ ?_
  simp only [permGroup, Fin.isValue, Pi.inv_apply, ne_eq, coe_univ, Set.subset_univ]

lemma N_pow_sum_invariant {n : ℕ} (m : ℕ) (f : (permGroup n)) (S : (SMRHNPlusU1 n).charges) :
    ∑ i, ((fun a => a^m) ∘ N.toFun (permCharges f S)) i= ∑ i, ((fun a => a^m) ∘ N.toFun S) i := by
  erw [mkFromSpecies_N]
  change  ∑ i : Fin n, ((fun a => a ^ m) ∘ _) (⇑(f⁻¹ _) i) = ∑ i : Fin n, ((fun a => a ^ m) ∘ _) i
  refine Equiv.Perm.sum_comp _ _ _ ?_
  simp only [permGroup, Fin.isValue, Pi.inv_apply, ne_eq, coe_univ, Set.subset_univ]

end invariantSums

section invariantACCs

open SMRHNPlusU1ACCs

lemma accGrav_invariant {n : ℕ} (f : (permGroup n)) (S : (SMRHNPlusU1 n).charges) :
    accGrav (permCharges f S) = accGrav S := by
  refine accGrav_eq_of_sum_eq ?_ ?_ ?_ ?_ ?_ ?_
  simpa using (@Q_pow_sum_invariant n 1 f S)
  simpa using (@U_pow_sum_invariant n 1 f S)
  simpa using (@D_pow_sum_invariant n 1 f S)
  simpa using (@L_pow_sum_invariant n 1 f S)
  simpa using (@E_pow_sum_invariant n 1 f S)
  simpa using (@N_pow_sum_invariant n 1 f S)


lemma accSU2_invariant {n : ℕ} (f : (permGroup n)) (S : (SMRHNPlusU1 n).charges) :
    accSU2 (permCharges f S) = accSU2 S := by
  refine accSU2_eq_of_sum_eq ?_ ?_
  simpa using (@Q_pow_sum_invariant n 1 f S)
  simpa using (@L_pow_sum_invariant n 1 f S)


lemma accSU3_invariant {n : ℕ} (f : (permGroup n)) (S : (SMRHNPlusU1 n).charges) :
    accSU3 (permCharges f S) = accSU3 S := by
  refine accSU3_eq_of_sum_eq ?_ ?_ ?_
  simpa using (@Q_pow_sum_invariant n 1 f S)
  simpa using (@U_pow_sum_invariant n 1 f S)
  simpa using (@D_pow_sum_invariant n 1 f S)

lemma accYY_invariant {n : ℕ} (f : (permGroup n)) (S : (SMRHNPlusU1 n).charges) :
    accYY (permCharges f S) = accYY  S := by
  refine accYY_eq_of_sum_eq ?_ ?_ ?_ ?_ ?_
  simpa using (@Q_pow_sum_invariant n 1 f S)
  simpa using (@U_pow_sum_invariant n 1 f S)
  simpa using (@D_pow_sum_invariant n 1 f S)
  simpa using (@L_pow_sum_invariant n 1 f S)
  simpa using (@E_pow_sum_invariant n 1 f S)

lemma accQuad_invariant {n : ℕ} (f : (permGroup n)) (S : (SMRHNPlusU1 n).charges) :
    accQuad.toFun (permCharges f S) = accQuad.toFun S :=
  accQuad_eq_of_sum_sq_eq
    (Q_pow_sum_invariant 2 f S)
    (U_pow_sum_invariant 2 f S)
    (D_pow_sum_invariant 2 f S)
    (L_pow_sum_invariant 2 f S)
    (E_pow_sum_invariant 2 f S)

lemma accCube_invariant {n : ℕ} (f : (permGroup n)) (S : (SMRHNPlusU1 n).charges) :
    accCube.toFun (permCharges f S) = accCube.toFun S :=
  accCube_eq_of_sum_cube_eq
    (Q_pow_sum_invariant 3 f S)
    (U_pow_sum_invariant 3 f S)
    (D_pow_sum_invariant 3 f S)
    (L_pow_sum_invariant 3 f S)
    (E_pow_sum_invariant 3 f S)
    (N_pow_sum_invariant 3 f S)

end invariantACCs


def SMRHNPlusU1FamilyPermutations (n : ℕ) : ACCSystemGroupAction (SMRHNPlusU1 n) where
  group := permGroup n
  groupInst := inferInstance
  rep := permCharges
  linearInvariant := by
    intro i
    simp at i
    match i with
    | 0 => exact accGrav_invariant
    | 1 => exact accSU2_invariant
    | 2 => exact accSU3_invariant
    | 3 => exact accYY_invariant
  quadInvariant := by
    intro i
    simp at i
    match i with
    | 0 => exact accQuad_invariant
  cubicInvariant := accCube_invariant
