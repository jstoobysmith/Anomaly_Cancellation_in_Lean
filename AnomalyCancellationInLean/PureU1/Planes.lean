/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.PureU1.Basic
import Mathlib.Tactic.Polyrith
import Mathlib.RepresentationTheory.Basic

def Γ₁ {n : ℕ} (f : Fin n → ℚ) : (PureU1 (2 * n)).AnomalyFree where
  val :=
