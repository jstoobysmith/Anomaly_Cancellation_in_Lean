/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.PureU1.Six.Basic
import Mathlib.Tactic.Polyrith

universe v u

open Nat
open  Finset

namespace PureU1
namespace Six

structure linearParameters where
  x1 : ℚ
  x2 : ℚ
  x3 : ℚ
  x4 : ℚ
  x5 : ℚ

@[ext]
lemma linearParameters.ext {S T : linearParameters}
    (h1 : S.x1 = T.x1) (h2 : S.x2 = T.x2) (h3 : S.x3 = T.x3) (h4 : S.x4 = T.x4)
    (h5 : S.x5 = T.x5) : S = T := by
  cases' S
  simp_all only

def linearParameterization : linearParameters ≃ AnomalyFreeLinear where
  toFun S := ⟨⟨S.x1, S.x2, S.x3, S.x4, S.x5, - (S.x1 + S.x2 + S.x3 + S.x4 + S.x5)⟩,
    by simp; ring ⟩
  invFun S := ⟨S.1.x1, S.1.x2, S.1.x3, S.1.x4, S.1.x5⟩
  left_inv S := by
    apply linearParameters.ext <;> rfl
  right_inv S := by
    apply AnomalyFreeLinear.ext
    apply Charges.ext
    any_goals rfl
    have hS := S.Grav
    simp at hS
    linear_combination - hS


end Six
end PureU1
