/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.SMRHNPlusU1.Basic
import AnomalyCancellationInLean.SMRHNPlusU1.FamilyUniversal
import Mathlib.Tactic.Polyrith
import AnomalyCancellationInLean.GroupActions

universe v u

namespace SMRHNPlusU1
open SMRHNPlusU1Charges
open SMRHNPlusU1ACCs
open BigOperators

@[simps!]
def hyperChargeOneFamily : (SMRHNPlusU1 1).AnomalyFree where
  val := fun i =>
    match i with
    | 0 => 1
    | 1 => -4
    | 2 => 2
    | 3 => -3
    | 4 => 6
    | 5 => 0
  linearSol := by
    intro i
    simp at i
    match i with
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl
  quadSol := by
    intro i
    simp at i
    match i with
    | 0 => rfl
  cubicSol := by rfl

end SMRHNPlusU1
