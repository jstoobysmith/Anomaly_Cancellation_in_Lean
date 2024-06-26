/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.PureU1.Permutations


universe v u

open Nat
open  Finset

namespace PureU1

variable {n : ℕ}

namespace One

theorem solEqZero (S : (PureU1 1).LinSols) : S = 0 := by
  apply ACCSystemLinear.LinSols.ext
  have hLin := pureU1_linear S
  simp at hLin
  funext i
  simp at i
  rw [show i = (0 : Fin 1) by omega]
  exact hLin

end One

end PureU1
