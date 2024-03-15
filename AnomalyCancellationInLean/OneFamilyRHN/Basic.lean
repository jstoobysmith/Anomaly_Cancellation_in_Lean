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



namespace OneFamily

section Charges
structure Charges where
  Q : ℚ
  U : ℚ
  D : ℚ
  L : ℚ
  E : ℚ
  N : ℚ

@[ext]
theorem Charge.ext {a b : Charges}
    (hQ : a.Q = b.Q)
    (hU : a.U = b.U)
    (hD : a.D = b.D)
    (hL : a.L = b.L)
    (hE : a.E = b.E)
    (hN : a.N = b.N) :
    a = b := by
  cases' a
  simp_all only


end Charges


/-- The anomaly cancelation condition for the gravity anomaly. -/
@[simp]
def accGrav (S : Charges) : ℚ :=
  6 * S.Q + 3 * S.U + 3 * S.D + 2 * S.L + S.E + S.N

end OneFamily
