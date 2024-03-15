/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Tactic.Polyrith
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.NumberTheory.FLT.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import AnomalyCancellationInLean.Basic
/-!

# Anomaly cancellation conditions for SM one family

The anomaly cancellation conditions for the `SU(3) × SU(2)` with the SM representations for one
family.

## Charges

- Define a structure `Charges`.
- Prove an extensionality theorem for `Charges`, `Charges.ext`.
- Define the structure of an additive commutative monoid on `Charges`, `chargesAddCommMonoid`.
- Define the structure of a module over `ℚ` on `Charges`, `chargesModule`.

## Linear anomaly cancellation conditions

- Define a linear map `Charges →ₗ[ℚ] ℚ` for each of the linear anomaly equations  `accGrav`,
  `accSU2`, `accSU3` and `accYY`.
- Define a structure `AnomalyFreeLinear` representing those charges which satisfy the linear ACCs.
- Prove an extensionality theorem for `AnomalyFreeLinear`, `AnomalyFreeLinear.ext`.
- Define the structure of an additive commutative monoid on `AnomalyFreeLinear`,
  `anomalyFreeLinearAddCommMonoid`.
- Define the structure of a module over `ℚ`  on `AnomalyFreeLinear`, `anomalyFreeLinearModule`.

## Anomaly cancellation conditions

- Define an equivariant function from `Charges` to `ℚ` (with the action αₐ b = a^n b on ℚ) for the
quadratic `accQaud` and cubic `accCube` anomaly equations.
- Define a structure `AnomalyFree` representing those charges which satisfy all the ACCs.
- Prove an extensionality theorem for `AnomalyFree`, `AnomalyFree.ext`.
- Define a multiplicative action of `ℚ` on `AnomallyFree`, `AnomalyFreeMulAction`.

-/

namespace SMOneFamily

structure Charges where
  Q : ℚ
  U : ℚ
  D : ℚ
  L : ℚ
  E : ℚ

@[ext]
lemma Charges.ext {S T : Charges}
  (hQ : S.Q = T.Q) (hU : S.U = T.U) (hD : S.D = T.D) (hL : S.L = T.L) (hE : S.E = T.E) : S = T := by
  cases' S
  simp_all only

@[simps!]
def equiv : Charges ≃ (Fin 5 → ℚ) where
  toFun S := fun i =>
    match i with
    | 0 => S.Q
    | 1 => S.U
    | 2 => S.D
    | 3 => S.L
    | 4 => S.E
  invFun f := ⟨f 0, f 1, f 2, f 3, f 4⟩
  left_inv S := by
    apply Charges.ext <;> rfl
  right_inv f := by
    funext i
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl
    | 4 => rfl
def Charges' : Type := Fin 5 → ℚ

@[simps!]
def SMOneFamilyCharges : ACCSystemCharges := ACCSystemChargesMk 5

@[simp]
def _root_.ACCSystemCharges.charges.Q (S : SMOneFamilyCharges.charges) : ℚ := S 0
@[simp]
def _root_.ACCSystemCharges.charges.U (S : SMOneFamilyCharges.charges) : ℚ := S 1
@[simp]
def _root_.ACCSystemCharges.charges.D (S : SMOneFamilyCharges.charges) : ℚ := S 2
@[simp]
def _root_.ACCSystemCharges.charges.L (S : SMOneFamilyCharges.charges) : ℚ := S 3
@[simp]
def _root_.ACCSystemCharges.charges.E (S : SMOneFamilyCharges.charges) : ℚ := S 4


def accGrav : (SMOneFamilyCharges.charges →ₗ[ℚ] ℚ) where
  toFun S := 6 * S.Q + 3 * S.U + 3 * S.D + 2 * S.L + S.E
  map_add' S T := by
    rw [SMOneFamilyCharges.chargesAddCommMonoid_add]
    simp
    ring
  map_smul' a S := by
    simp
    ring_nf
    rfl

def accSU2 : (SMOneFamilyCharges.charges →ₗ[ℚ] ℚ) where
  toFun S := 3 * S.Q + S.L
  map_add' S T := by
    rw [SMOneFamilyCharges.chargesAddCommMonoid_add]
    simp
    ring
  map_smul' a S := by
    simp
    ring_nf
    rfl

def accSU3 : (SMOneFamilyCharges.charges →ₗ[ℚ] ℚ) where
  toFun S := 2 * S.Q + S.U + S.D
  map_add' S T := by
    rw [SMOneFamilyCharges.chargesAddCommMonoid_add]
    simp
    ring
  map_smul' a S := by
    simp
    ring_nf
    rfl

/-- The anomaly cancelation condition for Y anomaly. -/
@[simp]
def accCube :
    (@MulActionHom ℚ SMOneFamilyCharges.charges _ ℚ cubeActionSMUL) where
  toFun S := 6 * S.Q^3 + 3 * S.U^3 + 3 * S.D^3 + 2 * S.L^3 + S.E^3
  map_smul' a S := by
    simp [HSMul.hSMul, SMul.smul]
    ring



end SMOneFamily

@[simps!]
def SMOneFamily: ACCSystem where
  numberLinear := 3
  linearACCs := fun i =>
    match i with
    | 0 => SMOneFamily.accGrav
    | 1 => SMOneFamily.accSU2
    | 2 => SMOneFamily.accSU3
  numberQuadratic := 0
  quadraticACCs := Fin.elim0
  cubicACC := SMOneFamily.accCube
