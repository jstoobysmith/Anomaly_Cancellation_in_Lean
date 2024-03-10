/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.GroupWithZero.Units.Lemmas

universe v u
open Nat

structure oneFamilyCharge where
  Q : ℚ
  U : ℚ
  D : ℚ
  L : ℚ
  E : ℚ
  N : ℚ

namespace oneFamilyCharge

@[ext]
theorem ext {a b : oneFamilyCharge}
    (hQ : a.Q = b.Q)
    (hU : a.U = b.U)
    (hD : a.D = b.D)
    (hL : a.L = b.L)
    (hE : a.E = b.E)
    (hN : a.N = b.N) :
    a = b := by
  cases' a
  simp_all only

end oneFamilyCharge

section theACCs

/-- The anomaly cancelation condition for the gravity anomaly. -/
@[simp]
def accGrav₁ (S : oneFamilyCharge) : ℚ :=
  6 * S.Q + 3 * S.U + 3 * S.D + 2 * S.L + S.E + S.N



end theACCs
