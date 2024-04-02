/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.PureU1.Sort
import AnomalyCancellationInLean.PureU1.BasisLinear
import Mathlib.Logic.Equiv.Fin
universe v u

open Nat
open  Finset
open BigOperators

namespace PureU1

variable {n : ℕ}

/--
  Given a natural number `n`, this lemma proves that `n + n` is equal to `2 * n`.
-/
lemma split_equal (n : ℕ) : n + n = 2 * n := (Nat.two_mul n).symm


lemma split_odd (n : ℕ) : n + 1 + n = 2 * n + 1 := by omega

@[simp]
def vectorLikeEven {n : ℕ}  (S : (PureU1 (2 * n)).charges) : Prop :=
  ∀ (i : Fin n), (sort S) (Fin.cast (split_equal n)  (Fin.castAdd n i))
  = - (sort S) (Fin.cast (split_equal n)  (Fin.natAdd n i))



end PureU1

