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

namespace Two

def equiv : (PureU1 2).AnomalyFreeLinear ≃ (PureU1 2).AnomalyFree where
  toFun S := ⟨⟨S, by intro i; simp at i; exact Fin.elim0 i⟩, by
    have hLin := pureU1_linear S
    rw [Fin.sum_univ_two] at hLin
    erw [accCube_explicit]
    simp
    rw [show S.val 0 = - S.val 1 by linear_combination hLin]
    ring⟩
  invFun S := S.1.1
  left_inv S := rfl
  right_inv S := rfl

end Two

end PureU1
