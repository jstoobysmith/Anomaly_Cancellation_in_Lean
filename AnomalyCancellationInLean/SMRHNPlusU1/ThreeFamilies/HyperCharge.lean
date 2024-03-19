/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.SMRHNPlusU1.Basic
import AnomalyCancellationInLean.SMRHNPlusU1.FamilyUniversal
import AnomalyCancellationInLean.SMRHNPlusU1.OneFamily.HyperCharge
import Mathlib.Tactic.Polyrith
import AnomalyCancellationInLean.GroupActions

universe v u

namespace SMRHNPlusU1
open SMRHNPlusU1Charges
open SMRHNPlusU1ACCs
open BigOperators

def hyperChargeNFamily (n : ℕ) : (SMRHNPlusU1 n).AnomalyFree :=
  (familyUniversalHom n).anomalyFree hyperChargeOneFamily



end SMRHNPlusU1
