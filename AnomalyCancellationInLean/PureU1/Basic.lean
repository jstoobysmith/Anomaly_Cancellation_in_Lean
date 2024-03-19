/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.BigOperators.Ring
import AnomalyCancellationInLean.Basic

universe v u
open Nat


open  Finset

namespace PureU1

@[simps!]
def PureU1Charges (n : ℕ) : ACCSystemCharges := ACCSystemChargesMk n

open BigOperators in
def accGrav (n : ℕ) : ((PureU1Charges n).charges →ₗ[ℚ] ℚ) where
  toFun S := ∑ i : Fin n, S i
  map_add' S T := Finset.sum_add_distrib
  map_smul' a S := by
   simp [HSMul.hSMul, SMul.smul]
   rw [← Finset.mul_sum]
   rfl

open BigOperators in
@[simp]
def accCube (n : ℕ)  : HomogeneousCubic ((PureU1Charges n).charges) where
  toFun S := ∑ i : Fin n, ((fun a => a^3) ∘ S) i
  map_smul' a S := by
   simp [HSMul.hSMul, SMul.smul]
   rw [Finset.mul_sum]
   ring_nf

end PureU1

@[simps!]
def PureU1 (n : ℕ): ACCSystem where
  numberLinear := 1
  linearACCs := fun i =>
    match i with
    | 0 => PureU1.accGrav n
  numberQuadratic := 0
  quadraticACCs := Fin.elim0
  cubicACC := PureU1.accCube n
