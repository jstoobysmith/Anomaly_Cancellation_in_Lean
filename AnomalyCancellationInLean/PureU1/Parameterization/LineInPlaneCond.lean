/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.PureU1.Basic
import AnomalyCancellationInLean.PureU1.Permutations
import AnomalyCancellationInLean.PureU1.VectorLike
import AnomalyCancellationInLean.PureU1.ConstAbs
import Mathlib.Tactic.Polyrith
import Mathlib.RepresentationTheory.Basic

-- https://arxiv.org/pdf/1912.04804.pdf

namespace PureU1

open BigOperators

variable {n : ℕ}


def lineInPlaneProp : ℚ × ℚ × ℚ → Prop := fun s =>
  s.1 = s.2.1 ∨ s.1 = - s.2.1 ∨ 2 * s.2.2 + s.1 + s.2.1 = 0

def lineInPlaneCond (S : (PureU1 (n)).AnomalyFreeLinear) : Prop :=
  ∀ (i1 i2 i3 : Fin (n)) (_ : i1 ≠ i2) (_ : i2 ≠ i3) (_ : i1 ≠ i3),
  lineInPlaneProp (S.val i1, (S.val i2, S.val i3))

lemma lineInPlaneCond_perm {S : (PureU1 (n)).AnomalyFreeLinear} (hS : lineInPlaneCond S)
    (M : (FamilyPermutations n).group) :
    lineInPlaneCond ((FamilyPermutations n).repAnomalyFreeLinear M S) := by
  intro i1 i2 i3 h1 h2 h3
  rw [FamilyPermutations_anomalyFreeLinear_apply, FamilyPermutations_anomalyFreeLinear_apply,
    FamilyPermutations_anomalyFreeLinear_apply]
  refine hS (M.invFun i1) (M.invFun i2) (M.invFun i3) ?_ ?_ ?_
  all_goals simp_all only [ne_eq, Equiv.invFun_as_coe, EmbeddingLike.apply_eq_iff_eq,
    not_false_eq_true]


lemma lineInPlaneCond_eq_last' {S : (PureU1 (n.succ.succ)).AnomalyFreeLinear} (hS : lineInPlaneCond S)
   (h : ¬ (S.val ((Fin.last n).castSucc))^2 = (S.val ((Fin.last n).succ))^2 ) :
    (2 - n) * S.val (Fin.last (n + 1)) =
    - (2 - n)* S.val (Fin.castSucc (Fin.last n)) := by
  erw [sq_eq_sq_iff_eq_or_eq_neg] at h
  rw [lineInPlaneCond] at hS
  simp only [lineInPlaneProp] at hS
  simp [not_or] at h
  have h1 (i : Fin n) : S.val i.castSucc.castSucc =
      - (S.val ((Fin.last n).castSucc) +  (S.val ((Fin.last n).succ))) / 2 := by
    have h1S := hS (Fin.last n).castSucc ((Fin.last n).succ) i.castSucc.castSucc
      (by simp; rw [Fin.ext_iff]; simp; omega)
      (by simp; rw [Fin.ext_iff]; simp; omega)
      (by simp; rw [Fin.ext_iff]; simp; omega)
    simp_all
    field_simp
    linear_combination h1S
  have h2 := pureU1_last S
  rw [Fin.sum_univ_castSucc] at h2
  simp [h1] at h2
  field_simp at h2
  linear_combination h2

lemma lineInPlaneCond_eq_last {S : (PureU1 (n.succ.succ.succ.succ.succ)).AnomalyFreeLinear}
    (hS : lineInPlaneCond S) :
    constAbsProp
    ((S.val ((Fin.last n.succ.succ.succ).castSucc)), (S.val ((Fin.last n.succ.succ.succ).succ)))
    := by
  rw [constAbsProp]
  by_contra hn
  have h := lineInPlaneCond_eq_last' hS hn
  rw [sq_eq_sq_iff_eq_or_eq_neg] at hn
  simp [or_not] at hn
  have hx : ((2 : ℚ) - ↑(n + 3))  ≠ 0 := by
    rw [Nat.cast_add]
    simp
    apply Not.intro
    intro a
    linarith
  have ht : S.val ((Fin.last n.succ.succ.succ).succ)  =
   - S.val  ((Fin.last n.succ.succ.succ).castSucc) := by
    rw [← mul_right_inj' hx]
    simp [Nat.succ_eq_add_one]
    simp at h
    rw [h]
    ring
  simp_all

lemma linesInPlane_eq_sq {S : (PureU1 (n.succ.succ.succ.succ.succ)).AnomalyFreeLinear}
    (hS : lineInPlaneCond S) : ∀ (i j : Fin n.succ.succ.succ.succ.succ) (_ : i ≠ j),
    constAbsProp (S.val i, S.val j) := by
  have hneq : ((Fin.last n.succ.succ.succ).castSucc) ≠ ((Fin.last n.succ.succ.succ).succ) := by
    simp [Fin.ext_iff]
  refine Prop_two constAbsProp hneq ?_
  intro M
  exact lineInPlaneCond_eq_last (lineInPlaneCond_perm hS M)

theorem linesInPlane_constAbs {S : (PureU1 (n.succ.succ.succ.succ.succ)).AnomalyFreeLinear}
      (hS : lineInPlaneCond S) : constAbs S.val := by
  intro i j
  by_cases hij : i ≠ j
  exact linesInPlane_eq_sq hS i j hij
  simp at hij
  rw [hij]



end PureU1
