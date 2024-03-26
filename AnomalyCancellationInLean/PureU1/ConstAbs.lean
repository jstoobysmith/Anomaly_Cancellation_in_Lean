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



lemma sorted_at_zero {S : (PureU1 (n.succ)).AnomalyFreeLinear}
    (hS : sorted S.val) (h : constAbs S.val) : S.val 0 ≤ 0 := by
  by_contra hi
  simp at hi
  have ht : 0 ≤ S.val 0 := by
     linarith
  have hall (i : Fin (n.succ)) : S.val i = S.val 0 := by
    refine sorted_gt_eq hS h ht i ?_
    simp
  have hl := pureU1_linear S
  simp [hall] at hl
  cases hl <;> rename_i h
  simp at h
  linarith
  simp_all

lemma sorted_at_last {S : (PureU1 (n.succ)).AnomalyFreeLinear}
    (hS : sorted S.val) (h : constAbs S.val) : 0 ≤ S.val (Fin.last n) := by
  by_contra hi
  have ht :  S.val ((Fin.last (n))) ≤ 0 := by
     linarith
  have hall (i : Fin n.succ) := sorted_lt_eq hS h ht i (by rw [Fin.le_def]; simp; omega)
  have hl := pureU1_linear S
  simp [hall] at hl
  cases hl <;> rename_i h
  simp at h
  linarith
  simp_all

lemma boundary_exists {S : (PureU1 (n.succ)).AnomalyFreeLinear}
    (hS : sorted S.val) (h : constAbs S.val)  (h0 : S.val 0 ≠ 0) :
    ∃ (k : Fin n), S.val k.castSucc < 0 ∧ 0 < S.val k.succ := by
  by_contra hk
  simp at hk
  have hzero (i : ℕ) (hi : i < n.succ) : S.val ⟨i, hi⟩ < 0 := by
    induction i
    have ht := sorted_at_zero hS h
    simp
    rw [lt_iff_le_and_ne]
    simp_all
    rename_i i hii
    have hi2 : i < n := by
      linarith
    have hi3 :  i < n.succ := by
      linarith
    let is : Fin (n) := ⟨i, hi2⟩
    have hk2 := hk is (hii hi3)
    rw [lt_iff_le_and_ne]
    have hl : (is.succ) = ⟨i.succ, hi⟩ := by
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
  have hlast : 0 < S.val (Fin.last n) := by
    rw [lt_iff_le_and_ne]
    have ht := h 0 (Fin.last n)
    have h0 : 0 ≠  S.val (Fin.last n)  := by
      symm
      rw [sq_eq_sq_iff_eq_or_eq_neg] at ht
      by_contra h0n
      rw [h0n] at ht
      simp at ht
      simp_all
    simp_all
    exact sorted_at_last hS h
  let iv := n
  have hiv : iv < n.succ := by omega
  have hlast2 := hzero iv hiv
  have ht : ⟨iv, hiv⟩ = Fin.last n := by
    rw [Fin.ext_iff]
    simp
  rw [ht] at hlast2
  exact lt_irrefl _ (hlast2.trans hlast)

lemma k_sum_cast (k : Fin  n) : k.succ.val + (n.succ - k.succ.val) = n.succ := by
  omega

lemma sum_with_boundary {S : (PureU1 n.succ).charges}
    (hS : sorted S) (hij : constAbs S) (k : Fin n)
    (hk1 : S k.castSucc < 0) (hk2 : 0 < S k.succ) :
    (accGrav (n.succ)) S = (2 * ↑↑k + 1 - ↑n) * S 0  := by
  simp [accGrav]
  have h : ∑ i : Fin (n.succ), S i  =
    ∑ i : Fin (k.succ.val + (n.succ - k.succ.val)), S (Fin.cast (k_sum_cast k) i):= by
    erw [Finset.sum_equiv (Fin.castIso (k_sum_cast k)).toEquiv]
    intro i
    simp
    intro i
    simp
    rfl
  rw [h]
  rw [Fin.sum_univ_add]
  have hfst (i : Fin k.succ.val) :
      S (Fin.cast (k_sum_cast k) (Fin.castAdd (n.succ - k.succ.val) i)) = S k.castSucc := by
    apply sorted_lt_eq hS hij
    simp_all
    rw [le_iff_eq_or_lt]
    simp_all
    rw [Fin.le_def]
    simp
    omega
  have hsnd (i : Fin (n.succ - k.succ.val)) :
      S (Fin.cast (k_sum_cast k)  (Fin.natAdd (k.succ.val) i)) = S k.succ := by
    apply sorted_gt_eq hS hij
    rw [le_iff_eq_or_lt]
    simp_all
    rw [Fin.le_def]
    simp
  simp only [hfst, hsnd]
  simp
  have h0 : S k.castSucc = S 0 := by
    symm
    apply sorted_lt_eq hS hij
    rw [le_iff_eq_or_lt]
    simp_all
    simp
  have hn : S k.succ = - S 0 := by
    have hsq := hij 0 k.succ
    rw [sq_eq_sq_iff_eq_or_eq_neg] at hsq
    have ht :  S 0 ≠ S k.succ := by
      have hl : S 0 < 0 := by
        rw [← h0]
        exact hk1
      by_contra  hn
      rw [hn] at hl
      exact lt_irrefl _ (hl.trans hk2)
    simp_all
  erw [h0, hn]
  ring

lemma boundary_value_odd_sorted (S : (PureU1 (2 * n + 1)).AnomalyFreeLinear) (hS : sorted S.val)
    (hij : constAbs S.val) :
    S = 0 := by
  by_cases h0 : S.val 0 ≠ 0
  obtain ⟨k, hk⟩ := boundary_exists hS hij h0
  have hgrav := pureU1_linear S
  change (accGrav (2 * n + 1)) S.val = 0 at hgrav
  have hk2 := sum_with_boundary hS hij k hk.1 hk.2
  rw [hgrav] at hk2
  simp at hk2
  cases hk2 <;> rename_i h
  have h1 : 2 * n = 2 * k.val + 1 := by
    rw [← @Nat.cast_inj ℚ]
    simp
    linear_combination -(1 * h)
  omega
  apply ACCSystemLinear.AnomalyFreeLinear.ext
  funext i
  have hi := hij i 0
  rw [h] at hi
  simp at hi
  rw [hi]
  rfl
  simp at h0
  apply ACCSystemLinear.AnomalyFreeLinear.ext
  funext i
  have hi := hij i 0
  rw [h0] at hi
  simp at hi
  rw [hi]
  rfl


theorem boundary_value_odd (S : (PureU1 (2 * n + 1)).AnomalyFreeLinear) (hij : constAbs S.val) :
    S = 0 :=
  have hS := constAbs_sort hij
  have hsor := sort_sorted S.val
  sortAFL_zero S (boundary_value_odd_sorted (sortAFL S) hsor hS)


lemma n_plus_n_eq_2n (n : ℕ) : n.succ + n.succ = 2 * n.succ := (Nat.two_mul n.succ).symm

lemma boundary_value_even_sorted (S : (PureU1 (2 * n.succ)).AnomalyFreeLinear)
    (hS : sorted S.val) (hij : constAbs S.val) :
    ∀ i, S.val (Fin.cast (n_plus_n_eq_2n n)  (Fin.castAdd n.succ i)) = S.val 0
    ∧ S.val (Fin.cast (n_plus_n_eq_2n n)  (Fin.natAdd n.succ i)) = - S.val 0 := by
  by_cases h0 : S.val 0 ≠ 0
  obtain ⟨k, hk⟩ := boundary_exists hS hij h0
  have hk2 := sum_with_boundary hS hij k hk.1 hk.2
  have hgrav := pureU1_linear S
  change (accGrav (2 * n.succ)) S.val = 0 at hgrav
  erw [hgrav] at hk2
  simp at hk2
  simp_all
  have ht : (k.val : ℚ)  = n := by
    linear_combination hk2 / 2
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
    have hijt := hij (k.succ) 0
    rw [sq_eq_sq_iff_eq_or_eq_neg] at hijt
    by_contra hn
    simp_all
    have hc13 := sorted_lt_eq hS hij (le_of_lt hk.left) 0 (by simp)
    rw [← hc13] at hk
    exact lt_irrefl _ (hk.left.trans hk.right)
  intro i
  exact And.intro (hc1 i) (hc2 i)
  simp at h0
  intro i
  have h1 := hij (Fin.cast (n_plus_n_eq_2n n)  (Fin.castAdd (succ n) i)) 0
  have h2 := hij (Fin.cast (n_plus_n_eq_2n n)  (Fin.natAdd (succ n) i)) 0
  rw [h0] at h1 h2
  simp at h1 h2
  rw [h1, h2, h0]
  simp

theorem boundary_value_even (S : (PureU1 (2 * n.succ)).AnomalyFreeLinear) (hij : constAbs S.val) :
    vectorLikeEven S.val := by
  have hS := constAbs_sort hij
  have hsor := sort_sorted S.val
  have h1 := boundary_value_even_sorted (sortAFL S) hsor hS
  intro i
  rw [sortAFL_val] at h1
  erw [(h1 i).left, (h1 i).right]
  simp

end ConstAbs

end PureU1
