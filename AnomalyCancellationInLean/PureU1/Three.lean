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

lemma three_sol_zero (S : (PureU1 3).AnomalyFree) :  S.val (0 : Fin 3) = 0 ∨ S.val (1 : Fin 3) = 0
   ∨ S.val (2 : Fin 3) = 0 := by
  have hL := pureU1_linear S.1.1
  have hC := pureU1_cube S
  simp at hL hC
  rw [Fin.sum_univ_three] at hL hC
  have h0 : S.val (0 : Fin 3) = - S.val (1 : Fin 3) - S.val (2 : Fin 3) := by
    linear_combination hL
  rw [h0] at hC
  have h1 :
      (-S.val (1 : Fin 3) - S.val (2 : Fin 3)) ^ 3 + S.val (1 : Fin 3) ^ 3 + S.val (2 : Fin 3) ^ 3 =
      - 3 *  S.val (1 : Fin 3) * S.val (2 : Fin 3) * (S.val (1 : Fin 3) + S.val (2 : Fin 3)) := by
    ring
  rw [h1] at hC
  simp at hC
  cases hC <;> rename_i hC
  simp_all
  apply Or.inl
  rw [add_assoc, hC] at hL
  simpa using hL

def solOfLinear (S : (PureU1 3).AnomalyFreeLinear)
    (hS : S.val (0 : Fin 3) = 0 ∨ S.val (1 : Fin 3) = 0 ∨ S.val (2 : Fin 3) = 0) :
    (PureU1 3).AnomalyFree :=
  ⟨⟨S, by intro i; simp at i; exact Fin.elim0 i⟩, by
  simp
  change accCube _ _ = _
  rw [accCube_explicit, Fin.sum_univ_three]
  have hLin := pureU1_linear S
  simp at hLin
  rw [Fin.sum_univ_three] at hLin
  cases hS <;> rename_i hS
  rw [hS] at hLin
  have h0 : S.val (1 : Fin 3) = - S.val (2 : Fin 3) := by
    linear_combination hLin
  rw [hS, h0]
  ring
  cases hS <;> rename_i hS
  rw [hS] at hLin
  have h0 : S.val (0 : Fin 3) = - S.val (2 : Fin 3) := by
    linear_combination hLin
  rw [hS, h0]
  ring
  rw [hS] at hLin
  have h0 : S.val (0 : Fin 3) = - S.val (1 : Fin 3) := by
    linear_combination hLin
  rw [hS, h0]
  ring⟩

theorem solOfLinear_surjects (S : (PureU1 3).AnomalyFree) :
    ∃ (T : (PureU1 3).AnomalyFreeLinear) (hT : T.val (0 : Fin 3) = 0 ∨ T.val (1 : Fin 3) = 0
    ∨ T.val (2 : Fin 3) = 0),
    solOfLinear T hT = S := by
  use S.1.1
  use (three_sol_zero S)
  rfl



end PureU1
