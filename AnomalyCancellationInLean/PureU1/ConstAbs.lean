/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.PureU1.Sort

universe v u

open Nat
open  Finset
open BigOperators

namespace PureU1

variable {n : ℕ}

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

namespace ConstAbs

lemma sorted_lt_eq {S : (PureU1 n).charges}
    (hS : sorted S) (h : constAbs S) {k : Fin n}
    (hk : S k ≤ 0) : ∀ i ≤ k, S i = S k := by
  intro i hik
  have hSS := hS i k hik
  have ht := h i k
  rw [sq_eq_sq_iff_eq_or_eq_neg] at ht
  cases ht <;> rename_i h
  exact h
  linarith

lemma sorted_gt_eq {S : (PureU1 n).charges}
    (hS : sorted S) (h : constAbs S) {k : Fin n}
    (hk : 0 ≤ S k ) : ∀ (i : Fin n) (_ : k ≤ i), S i = S k := by
  intro i hik
  have hSS := hS k i hik
  have ht := h i k
  rw [sq_eq_sq_iff_eq_or_eq_neg] at ht
  cases ht <;> rename_i h
  exact h
  linarith


lemma k_sum_cast (k : Fin (2 * n + 1)) : k.succ.val + (2 * n.succ - k.succ.val) = 2 * n.succ := by
  omega

lemma sum_with_boundary_even {S : (PureU1 (2 * n.succ)).charges}
    (hS : sorted S) (hij : constAbs S) (k : Fin (2 * n + 1))
    (hk1 : S (Fin.cast minus_one_sum k.castSucc) < 0)
    (hk2 : 0 < S (Fin.cast minus_one_sum k.succ)) :
    (accGrav (2 * n.succ)) S = 2 * (↑↑k - n) * S 0 := by
  simp [accGrav]
  have h : ∑ i : Fin (2 * Nat.succ n), S i  =
    ∑ i : Fin (k.succ.val + (2 * n.succ - k.succ.val)), S (Fin.cast (k_sum_cast k) i):= by
    erw [Finset.sum_equiv (Fin.castIso (k_sum_cast k)).toEquiv]
    intro i
    simp
    intro i
    simp
    rfl
  rw [h]
  rw [Fin.sum_univ_add]
  have hfst (i : Fin k.succ.val) :
      S (Fin.cast (k_sum_cast k) (Fin.castAdd (2 * Nat.succ n - k.succ.val) i)) =
      S (Fin.cast minus_one_sum k.castSucc) := by
    apply sorted_lt_eq hS hij
    simp_all
    rw [le_iff_eq_or_lt]
    simp_all
    rw [Fin.le_def]
    simp
    omega
  have hsnd (i : Fin (2 * Nat.succ n - k.succ.val)) :
      S (Fin.cast (k_sum_cast k)  (Fin.natAdd (k.succ.val) i)) =
      S (Fin.cast minus_one_sum k.succ) := by
    apply sorted_gt_eq hS hij
    rw [le_iff_eq_or_lt]
    simp_all
    rw [Fin.le_def]
    simp
  simp only [hfst, hsnd]
  simp
  have h0 : S (Fin.cast minus_one_sum k.castSucc) = S 0 := by
    symm
    apply sorted_lt_eq hS hij
    rw [le_iff_eq_or_lt]
    simp_all
    simp
  have hn : S (Fin.cast minus_one_sum k.succ) = - S 0 := by
    have hsq := hij 0 (Fin.cast minus_one_sum k.succ)
    rw [sq_eq_sq_iff_eq_or_eq_neg] at hsq
    have ht :  S 0 ≠ S (Fin.cast minus_one_sum (Fin.succ k)) := by
      have hl : S 0 < 0 := by
        rw [← h0]
        exact hk1
      by_contra  hn
      rw [hn] at hl
      exact lt_irrefl _ (hl.trans hk2)
    simp_all
  erw [h0, hn]
  have ht : (↑↑k + 1) * S 0 + ↑(2 * Nat.succ n - (↑k + 1)) * - S 0 =
     (↑↑k + 1- ↑(2 * Nat.succ n - (↑k + 1))) * S 0 := by
    ring
  rw [ht]
  have hx : ↑k + 1 ≤ 2 * Nat.succ n := by
    omega
  rw [Nat.cast_sub hx]
  rw [Nat.cast_add, Nat.cast_mul]
  simp [Nat.succ_eq_add_one]
  ring_nf
  simp

lemma sorted_at_zero {S : (PureU1 (2 * n.succ)).AnomalyFreeLinear}
    (hS : sorted S.val) (h : constAbs S.val) : S.val 0 ≤ 0 := by
  by_contra hi
  simp at hi
  have ht : 0 ≤ S.val 0 := by
     linarith
  have hall (i : Fin (2 * n.succ)) : S.val i = S.val 0 := by
    refine sorted_gt_eq hS h ht i ?_
    simp
  have hl := pureU1_linear S
  simp [hall] at hl
  cases hl <;> rename_i h
  simp at h
  linarith
  simp_all

lemma minus_one_sum : 2 * n + 1 +1 = 2 * n.succ := by omega

lemma sorted_at_last {S : (PureU1 (2 * n.succ)).AnomalyFreeLinear}
    (hS : sorted S.val) (h : constAbs S.val) :
    0 ≤ S.val (Fin.cast minus_one_sum (Fin.last (2 * n +1))) := by
  by_contra hi
  have ht :  S.val (Fin.cast minus_one_sum (Fin.last (2* n +1))) ≤ 0 := by
     linarith
  have hall (i : Fin (2 * n.succ)) := sorted_lt_eq hS h ht i (by rw [Fin.le_def]; simp; omega)
  have hl := pureU1_linear S
  simp [hall] at hl
  cases hl <;> rename_i h
  simp at h
  linarith
  simp_all

lemma boundary_exists {S : (PureU1 (2 * n.succ)).AnomalyFreeLinear}
    (hS : sorted S.val) (h : constAbs S.val)  (h0 : S.val 0 ≠ 0) :
    ∃ (k : Fin (2 * n + 1)),
    S.val (Fin.cast minus_one_sum k.castSucc) < 0 ∧ 0 < S.val (Fin.cast minus_one_sum k.succ) := by
  by_contra hk
  simp at hk
  have hzero (i : ℕ) (hi : i < 2 * n.succ) : S.val ⟨i, hi⟩ < 0 := by
    induction i
    have ht := sorted_at_zero hS h
    simp
    rw [lt_iff_le_and_ne]
    simp_all
    rename_i i hii
    have hi2 : i < 2 * n + 1 := by
      linarith
    have hi3 :  i < 2 * Nat.succ n := by
      linarith
    let is : Fin (2 * n +1) := ⟨i, hi2⟩
    have hk2 := hk is (hii hi3)
    rw [lt_iff_le_and_ne]
    have hl : (Fin.cast minus_one_sum is.succ) = ⟨i.succ, hi⟩ := by
      rfl
    rw [← hl]
    have ht := h 0 ⟨i.succ, hi⟩
    have h0 : S.val ⟨i.succ, hi⟩ ≠ 0 := by
      rw [sq_eq_sq_iff_eq_or_eq_neg] at ht
      by_contra h0n
      rw [h0n] at ht
      simp at ht
      simp_all
    simp_all
  have hlast : 0 < S.val (Fin.cast minus_one_sum (Fin.last (2* n +1))) := by
    rw [lt_iff_le_and_ne]
    have ht := h 0 (Fin.cast minus_one_sum (Fin.last (2* n +1)))
    have h0 : 0 ≠  S.val (Fin.cast minus_one_sum (Fin.last (2* n +1)))  := by
      symm
      rw [sq_eq_sq_iff_eq_or_eq_neg] at ht
      by_contra h0n
      rw [h0n] at ht
      simp at ht
      simp_all
    simp_all
    exact sorted_at_last hS h
  let iv := 2 * n + 1
  have hiv : iv < 2 * n.succ := by omega
  have hlast2 := hzero iv hiv
  have ht : ⟨iv, hiv⟩ = (Fin.cast minus_one_sum (Fin.last (2* n +1))) := by
    rw [Fin.ext_iff]
    simp
  rw [ht] at hlast2
  exact lt_irrefl _ (hlast2.trans hlast)

lemma n_plus_n_eq_2n (n : ℕ) : n.succ + n.succ = 2 * n.succ := (Nat.two_mul n.succ).symm

lemma boundary_value {S : (PureU1 (2 * n.succ)).AnomalyFreeLinear}
    (hS : sorted S.val)
    (hij : constAbs S.val) (h0 : S.val 0 ≠ 0) :
    ∀ i,
    S.val (Fin.cast (n_plus_n_eq_2n n)  (Fin.castAdd n.succ i)) = S.val 0
    ∧
    S.val (Fin.cast (n_plus_n_eq_2n n)  (Fin.natAdd n.succ i)) = - S.val 0 := by
  obtain ⟨k, hk⟩ := boundary_exists hS hij h0
  have hk2 := sum_with_boundary_even hS hij k hk.1 hk.2
  have hgrav := pureU1_linear S
  change (accGrav (2 * Nat.succ n)) S.val = 0 at hgrav
  rw [hgrav] at hk2
  simp at hk2
  simp_all
  have ht : (k.val : ℚ)  = n := by
    linear_combination hk2
  have hl : k.val = n := by
    simp_all only [sub_self, Nat.cast_inj]
  have hc1 (i : Fin n.succ) :
      S.val (Fin.cast (n_plus_n_eq_2n n)  (Fin.castAdd n.succ i)) = S.val 0 := by
    have hc11 := sorted_lt_eq hS hij (le_of_lt hk.left) 0 (by simp)
    have hc12 := sorted_lt_eq hS hij (le_of_lt hk.left)
       (Fin.cast (n_plus_n_eq_2n n)  (Fin.castAdd n.succ i))
      (by rw [Fin.le_def]; simp; rw [hl]; omega)
    rw [hc11, hc12]
  have hc2  (i : Fin n.succ) :
      S.val (Fin.cast (n_plus_n_eq_2n n)  (Fin.natAdd n.succ i)) = - S.val 0 := by
    have hc11 := sorted_gt_eq hS hij
      (le_of_lt hk.right)
      (Fin.cast (n_plus_n_eq_2n n)  (Fin.natAdd n.succ i))
      (by rw [Fin.le_def]; simp; rw [hl]; omega)
    rw [hc11]
    have hijt := hij (Fin.cast minus_one_sum k.succ) 0
    rw [sq_eq_sq_iff_eq_or_eq_neg] at hijt
    by_contra hn
    simp_all
    have hc13 := sorted_lt_eq hS hij (le_of_lt hk.left) 0 (by simp)
    rw [← hc13] at hk
    exact lt_irrefl _ (hk.left.trans hk.right)
  intro i
  exact And.intro (hc1 i) (hc2 i)


end ConstAbs

end PureU1
