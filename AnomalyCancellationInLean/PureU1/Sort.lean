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

@[simp]
def sorted {n : ℕ}  (S : (PureU1 n).charges) : Prop :=
   ∀ i j (_ : i ≤ j),  S i ≤ S j

@[simp]
def sort {n : ℕ} (S : (PureU1 n).charges) : (PureU1 n).charges :=
  ((FamilyPermutations n).rep (Tuple.sort S).symm S)

lemma sort_sorted {n : ℕ} (S : (PureU1 n).charges) :  sorted (sort S) := by
  simp
  intro i j hij
  erw [FamilyPermutations_charges_apply, FamilyPermutations_charges_apply]
  exact Tuple.monotone_sort S hij

lemma sort_perm {n : ℕ} (S : (PureU1 n).charges) (M :(FamilyPermutations n).group) :
    sort ((FamilyPermutations n).rep M S) = sort S :=
  @Tuple.comp_perm_comp_sort_eq_comp_sort n ℚ _ S M⁻¹

lemma sort_projection {n : ℕ} (S : (PureU1 n).charges) : sort (sort S) = sort S :=
  sort_perm S (Tuple.sort S).symm


end PureU1
