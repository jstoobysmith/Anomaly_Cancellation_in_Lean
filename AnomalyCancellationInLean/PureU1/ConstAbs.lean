/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.PureU1.Sort
import AnomalyCancellationInLean.PureU1.VectorLike

universe v u

open Nat
open  Finset
open BigOperators

namespace PureU1

variable {n : ℕ}

def constAbsProp : ℚ × ℚ → Prop := fun s => s.1^2 = s.2^2

@[simp]
def constAbs (S : (PureU1 n).charges) : Prop := ∀ i j, (S i) ^ 2 = (S j) ^ 2

lemma constAbs_perm (S : (PureU1 n).charges) (M :(FamilyPermutations n).group) :
    constAbs ((FamilyPermutations n).rep M S) ↔ constAbs S := by
  simp
  apply Iff.intro
  intro h i j
  have h2 := h (M.toFun i) (M.toFun j)
  erw [FamilyPermutations_charges_apply, FamilyPermutations_charges_apply] at h2
  simp at h2
  exact h2
  intro h i j
  erw [FamilyPermutations_charges_apply, FamilyPermutations_charges_apply]
  exact h (M.invFun i) (M.invFun j)

lemma constAbs_sort {S : (PureU1 n).charges} (CA : constAbs S) : constAbs (sort S) := by
  rw [sort]
  exact (constAbs_perm S _).mpr CA

def constAbsSorted (S : (PureU1 n).charges) : Prop := constAbs S ∧ sorted S

namespace constAbsSorted
section charges

variable {S : (PureU1 n.succ).charges} {A : (PureU1 n.succ).LinSols}
variable (hS : constAbsSorted S) (hA : constAbsSorted A.val)

lemma lt_eq  {k i : Fin n.succ} (hk : S k ≤ 0) (hik : i ≤ k) : S i = S k := by
  have hSS := hS.2 i k hik
  have ht := hS.1 i k
  rw [sq_eq_sq_iff_eq_or_eq_neg] at ht
  cases ht <;> rename_i h
  exact h
  linarith

lemma val_le_zero  {i : Fin n.succ} (hi : S i ≤ 0) : S i = S (0 : Fin n.succ) := by
  symm
  apply lt_eq hS hi
  simp

lemma gt_eq {k i: Fin n.succ} (hk : 0 ≤ S k) (hik : k ≤ i) : S i = S k := by
  have hSS := hS.2 k i hik
  have ht := hS.1 i k
  rw [sq_eq_sq_iff_eq_or_eq_neg] at ht
  cases ht <;> rename_i h
  exact h
  linarith

lemma zero_gt (h0 : 0 ≤ S (0 : Fin n.succ)) (i : Fin n.succ) : S (0 : Fin n.succ) = S i := by
  symm
  refine gt_eq hS h0 ?_
  simp

lemma opposite_signs_eq_neg {i j : Fin n.succ} (hi : S i ≤ 0) (hj : 0 ≤ S j) : S i = - S j := by
  have hSS := hS.1 i j
  rw [sq_eq_sq_iff_eq_or_eq_neg] at hSS
  cases' hSS with h h
  simp_all
  linarith
  exact h

lemma is_zero (h0 : S (0 : Fin n.succ) = 0) : S = 0 := by
  funext i
  have ht := hS.1 i (0 : Fin n.succ)
  rw [h0] at ht
  simp at ht
  exact ht

@[simp]
def boundary (S : (PureU1 n.succ).charges) (k : Fin n) : Prop := S k.castSucc < 0 ∧ 0 < S k.succ

lemma boundary_castSucc {k : Fin n} (hk : boundary S k) : S k.castSucc = S (0 : Fin n.succ) :=
  (lt_eq hS (le_of_lt hk.left) (by simp : 0 ≤ k.castSucc)).symm

lemma boundary_succ {k : Fin n} (hk : boundary S k) : S k.succ = - S (0 : Fin n.succ) := by
  have hn := boundary_castSucc hS hk
  rw [opposite_signs_eq_neg hS (le_of_lt hk.left) (le_of_lt hk.right)] at hn
  linear_combination -(1 * hn)

lemma boundary_split (k : Fin n) :  k.succ.val + (n.succ - k.succ.val) = n.succ := by
  omega

lemma boundary_accGrav' (k : Fin n) : accGrav n.succ S =
    ∑ i : Fin (k.succ.val + (n.succ - k.succ.val)), S (Fin.cast (boundary_split k) i) := by
  simp [accGrav]
  erw [Finset.sum_equiv (Fin.castIso (boundary_split k)).toEquiv]
  intro i
  simp
  intro i
  simp
  rfl

lemma boundary_accGrav'' (k : Fin n) (hk : boundary S k) :
    accGrav n.succ S = (2 * ↑↑k + 1 - ↑n) * S (0 : Fin n.succ) := by
  rw [boundary_accGrav' k]
  rw [Fin.sum_univ_add]
  have hfst (i : Fin k.succ.val) :
      S (Fin.cast (boundary_split k) (Fin.castAdd (n.succ - k.succ.val) i)) = S k.castSucc := by
    apply lt_eq hS (le_of_lt hk.left) (by rw [Fin.le_def]; simp; omega)
  have hsnd (i : Fin (n.succ - k.succ.val)) :
      S (Fin.cast (boundary_split k)  (Fin.natAdd (k.succ.val) i)) = S k.succ := by
    apply gt_eq hS (le_of_lt hk.right) (by rw [Fin.le_def]; simp)
  simp only [hfst, hsnd]
  simp
  rw [boundary_castSucc hS hk, boundary_succ hS hk]
  ring

@[simp]
def hasBoundary (S : (PureU1 n.succ).charges) : Prop :=
  ∃ (k : Fin n), boundary S k

lemma not_hasBoundary_zero_le (hnot : ¬ (hasBoundary S)) (h0 : S (0 : Fin n.succ) < 0) :
    ∀ i, S (0 : Fin n.succ) = S i := by
  intro ⟨i, hi⟩
  simp at hnot
  induction i
  rfl
  rename_i i hii
  have hnott := hnot ⟨i, by {simp at hi; linarith} ⟩
  have hii := hii (by omega)
  erw [← hii] at hnott
  exact (val_le_zero hS (hnott h0)).symm

lemma not_hasBoundry_zero (hnot : ¬ (hasBoundary S)) (i : Fin n.succ) :
    S (0 : Fin n.succ) = S i := by
  by_cases hi : S (0 : Fin n.succ) < 0
  exact not_hasBoundary_zero_le hS hnot hi i
  simp at hi
  exact zero_gt hS hi i

lemma not_hasBoundary_grav (hnot :  ¬ (hasBoundary S)) :
    accGrav n.succ S = n.succ * S (0 : Fin n.succ) := by
  simp [accGrav, ← not_hasBoundry_zero hS hnot]


lemma AFL_hasBoundary (h : A.val (0 : Fin n.succ) ≠ 0) : hasBoundary A.val := by
  by_contra hn
  have h0 := not_hasBoundary_grav hA hn
  simp [accGrav] at h0
  erw [pureU1_linear A] at h0
  simp at h0
  cases' h0
  linarith
  simp_all

lemma AFL_odd_noBoundary {A : (PureU1 (2 * n + 1)).LinSols} (h : constAbsSorted A.val)
  (hA : A.val (0 : Fin (2*n +1)) ≠ 0) :
    ¬ hasBoundary A.val := by
  by_contra hn
  obtain ⟨k, hk⟩ := hn
  have h0 := boundary_accGrav'' h k hk
  simp [accGrav] at h0
  erw [pureU1_linear A] at h0
  simp [hA] at h0
  have h1 : 2 * n = 2 * k.val + 1 := by
    rw [← @Nat.cast_inj ℚ]
    simp
    linear_combination - h0
  omega

lemma AFL_odd_zero {A : (PureU1 (2 * n + 1)).LinSols} (h : constAbsSorted A.val) :
    A.val (0 : Fin (2 * n + 1)) = 0 := by
  by_contra hn
  exact (AFL_odd_noBoundary h hn ) (AFL_hasBoundary h hn)

theorem AFL_odd (A : (PureU1 (2 * n + 1)).LinSols) (h : constAbsSorted A.val) :
    A = 0 := by
  apply ACCSystemLinear.LinSols.ext
  exact  is_zero h (AFL_odd_zero h)

lemma AFL_even_Boundary {A : (PureU1 (2 * n.succ)).LinSols} (h : constAbsSorted A.val)
    (hA : A.val (0 : Fin (2 * n.succ)) ≠ 0) {k : Fin (2 * n + 1)} (hk : boundary A.val k) : k.val = n := by
  have h0 := boundary_accGrav'' h k hk
  change ∑ i : Fin (succ (Nat.mul 2 n + 1)), A.val i = _ at h0
  erw [pureU1_linear A] at h0
  simp [hA] at h0
  rw [← @Nat.cast_inj ℚ]
  linear_combination h0 / 2

lemma AFL_even_below' {A : (PureU1 (2 * n.succ)).LinSols} (h : constAbsSorted A.val)
    (hA : A.val  (0 : Fin (2 * n.succ)) ≠ 0) (i : Fin n.succ)  :
    A.val (Fin.cast (split_equal n.succ)  (Fin.castAdd n.succ i)) = A.val (0 : Fin (2*n.succ)) := by
  obtain ⟨k, hk⟩ := AFL_hasBoundary h hA
  rw [← boundary_castSucc h hk]
  apply lt_eq h (le_of_lt hk.left)
  rw [Fin.le_def]
  simp
  rw [AFL_even_Boundary h hA hk]
  omega

lemma AFL_even_below (A : (PureU1 (2 * n.succ)).LinSols) (h : constAbsSorted A.val)
    (i : Fin n.succ) :
     A.val (Fin.cast (split_equal n.succ)  (Fin.castAdd n.succ i)) = A.val (0 : Fin (2*n.succ)) := by
  by_cases hA : A.val (0 : Fin (2*n.succ)) = 0
  rw [is_zero h hA]
  simp
  rfl
  exact AFL_even_below' h hA i

lemma AFL_even_above' {A : (PureU1 (2 * n.succ)).LinSols} (h : constAbsSorted A.val)
    (hA : A.val (0 : Fin (2*n.succ)) ≠ 0) (i : Fin n.succ)  :
    A.val (Fin.cast (split_equal n.succ)  (Fin.natAdd n.succ i)) =
    - A.val (0 : Fin (2*n.succ)) := by
  obtain ⟨k, hk⟩ := AFL_hasBoundary h hA
  rw [← boundary_succ h hk]
  apply gt_eq h (le_of_lt hk.right)
  rw [Fin.le_def]
  simp
  rw [AFL_even_Boundary h hA hk]
  omega

lemma AFL_even_above (A : (PureU1 (2 * n.succ)).LinSols) (h : constAbsSorted A.val)
    (i : Fin n.succ) :
    A.val (Fin.cast (split_equal n.succ)  (Fin.natAdd n.succ i)) =
    - A.val (0 : Fin (2*n.succ)) := by
  by_cases hA : A.val (0 : Fin (2*n.succ)) = 0
  rw [is_zero h hA]
  simp
  rfl
  exact AFL_even_above' h hA i


end charges

end constAbsSorted


namespace ConstAbs

theorem boundary_value_odd (S : (PureU1 (2 * n + 1)).LinSols) (hs : constAbs S.val) :
    S = 0 :=
  have hS := And.intro (constAbs_sort hs) (sort_sorted S.val)
  sortAFL_zero S (constAbsSorted.AFL_odd (sortAFL S) hS)


theorem boundary_value_even (S : (PureU1 (2 * n.succ)).LinSols) (hs : constAbs S.val) :
    vectorLikeEven S.val := by
  have hS := And.intro (constAbs_sort hs) (sort_sorted S.val)
  intro i
  have h1 := constAbsSorted.AFL_even_below (sortAFL S) hS
  have h2 := constAbsSorted.AFL_even_above (sortAFL S) hS
  rw [sortAFL_val] at h1 h2
  rw [h1, h2]
  simp

end ConstAbs

end PureU1
