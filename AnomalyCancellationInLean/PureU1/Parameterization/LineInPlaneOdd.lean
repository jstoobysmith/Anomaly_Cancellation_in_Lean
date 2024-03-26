/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.PureU1.Basic
import AnomalyCancellationInLean.PureU1.Permutations
import AnomalyCancellationInLean.PureU1.VectorLike
import AnomalyCancellationInLean.PureU1.ConstAbs
import AnomalyCancellationInLean.PureU1.Parameterization.LineInPlaneCond
import Mathlib.Tactic.Polyrith
import Mathlib.RepresentationTheory.Basic

-- https://arxiv.org/pdf/1912.04804.pdf

namespace PureU1

open BigOperators

variable {n : ℕ}
open VectorLikeOddPlane

/-- The line from P to P! through S is within the cubic. -/
def lineInCubic (S : (PureU1 (2 * n + 1)).AnomalyFreeLinear) : Prop :=
  ∀ (g f : Fin n → ℚ)  (_ : S.val = Pa g f) (a b : ℚ) ,
  (PureU1.accCube (2 * n + 1)).toFun (a • P g + b • P! f) = 0

lemma line_in_cubic_P_P_P! {S : (PureU1 (2 * n + 1)).AnomalyFreeLinear} (h : lineInCubic S) :
    ∀ (g : Fin n → ℚ) (f : Fin n → ℚ) (_ : S.val =  P g + P! f),
    accCubeTriLinSymm.toFun (P g, P g, P! f) = 0 := by
  intro g f hS
  rw [lineInCubic] at h
  let h := h g f hS
  rw [accCube_from_tri] at h
  simp only [TriLinearSymm.toHomogeneousCubic_add] at h
  simp only [HomogeneousCubic.map_smul',
   accCubeTriLinSymm.map_smul₁, accCubeTriLinSymm.map_smul₂, accCubeTriLinSymm.map_smul₃] at h
  have h1 := h 0 1
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, PureU1Charges_charges,
    zero_mul, one_pow, one_mul, zero_add, accCubeTriLinSymm_toFun, mul_zero, add_zero] at h1
  rw [h1] at h
  have h2 := h 1 0
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, PureU1Charges_charges,
    zero_mul, one_pow, one_mul, zero_add, accCubeTriLinSymm_toFun, mul_zero, add_zero] at h2
  rw [h2] at h
  simp only [mul_zero, add_zero, zero_add] at h
  have h3 := h 1 1
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, PureU1Charges_charges,
    zero_mul, one_pow, one_mul, zero_add, mul_zero, add_zero] at h3
  have h4 := h 1 (-1)
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, PureU1Charges_charges,
    zero_mul, one_pow, one_mul, zero_add, mul_zero, add_zero] at h4
  linear_combination h3 / 6 + -1 * h4 / 6


/-- The line from P to P! through S is within the cubic for all permutations of S. -/
def lineInCubicPerm (S : (PureU1 (2 * n + 1)).AnomalyFreeLinear) : Prop :=
  ∀ (M : (FamilyPermutations (2 * n + 1)).group ),
    lineInCubic ((FamilyPermutations (2 * n + 1)).repAnomalyFreeLinear M S)

/-- If `lineInCubicPerm S` then `lineInCubic S`.  -/
lemma lineInCubicPerm_self {S : (PureU1 (2 * n + 1)).AnomalyFreeLinear} (hS : lineInCubicPerm S) :
    lineInCubic S := hS 1

/-- If `lineInCubicPerm S` then `lineInCubicPerm (M S)` for all permutations `M`. -/
lemma lineInCubicPerm_permute {S : (PureU1 (2 * n + 1)).AnomalyFreeLinear}
    (hS : lineInCubicPerm S) (M' : (FamilyPermutations (2 * n + 1)).group) :
    lineInCubicPerm ((FamilyPermutations (2 * n + 1)).repAnomalyFreeLinear M' S) := by
  rw [lineInCubicPerm]
  intro M
  have ht : (((ACCSystemGroupAction.repAnomalyFreeLinear (FamilyPermutations (2 * n + 1))) M)
    (((ACCSystemGroupAction.repAnomalyFreeLinear (FamilyPermutations (2 * n + 1))) M') S))
    = (ACCSystemGroupAction.repAnomalyFreeLinear (FamilyPermutations (2 * n + 1))) (M * M') S
      := by
    simp [(FamilyPermutations (2 * n.succ)).repAnomalyFreeLinear.map_mul']
  rw [ht]
  exact hS (M * M')


lemma lineInCubicPerm_swap {S : (PureU1 (2 * n.succ + 1)).AnomalyFreeLinear}
    (LIC : lineInCubicPerm S) :
    ∀ (j : Fin n.succ) (g f : Fin n.succ → ℚ) (_ : S.val = Pa g f) ,
      (S.val (δ!₂ j) - S.val (δ!₁ j))
      * accCubeTriLinSymm.toFun (P g, P g, basis!AsCharges j) = 0 := by
  intro j g f h
  let S' :=  (FamilyPermutations (2 * n.succ + 1)).repAnomalyFreeLinear
    (pairSwap (δ!₁ j) (δ!₂ j)) S
  have hSS' : ((FamilyPermutations (2 * n.succ + 1)).repAnomalyFreeLinear
    (pairSwap (δ!₁ j) (δ!₂ j))) S = S' := rfl
  obtain ⟨g', f', hall⟩ := span_basis_swap! j hSS' g f h
  have h1 := line_in_cubic_P_P_P! (lineInCubicPerm_self LIC) g f h
  have h2 := line_in_cubic_P_P_P!
    (lineInCubicPerm_self (lineInCubicPerm_permute LIC (pairSwap (δ!₁ j) (δ!₂ j)))) g' f' hall.1
  rw [hall.2.1, hall.2.2] at h2
  rw [accCubeTriLinSymm.map_add₃, h1, accCubeTriLinSymm.map_smul₃] at h2
  simpa using h2

lemma P_P_P!_accCube' {S : (PureU1 (2 * n.succ.succ + 1)).AnomalyFreeLinear}
    (f g : Fin n.succ.succ → ℚ) (hS : S.val = Pa f g) :
    accCubeTriLinSymm.toFun (P f, P f, basis!AsCharges 0) =
    (S.val (δ!₁ 0) + S.val (δ!₂ 0)) * (2 * S.val δ!₃ + S.val (δ!₁ 0) + S.val (δ!₂ 0)) := by
  rw [P_P_P!_accCube f 0]
  rw [← Pa_δa₁ f g]
  rw [← hS]
  have ht : δ!₁ (0 : Fin n.succ.succ) = δ₁ 1 := by
    simp [δ!₁, δ₁]
    rw [Fin.ext_iff]
    simp
  nth_rewrite 1 [ht]
  rw [P_δ₁]
  have h1 := Pa_δa₁ f g
  have h4 := Pa_δa₄ f g 0
  have h2 := Pa_δa₂ f g 0
  rw [← hS] at h1 h2 h4
  simp at h2
  have h5 : f 1 = S.val (δa₂ 0) +  S.val δa₁ +  S.val (δa₄ 0):= by
     linear_combination -(1 * h1) - 1 * h4 - 1 * h2
  rw [h5]
  rw [δa₄_δ!₂]
  have h0 : (δa₂ (0 : Fin n.succ)) = δ!₁ 0 := by
    rw [δa₂_δ!₁]
    simp
  rw [h0, δa₁_δ!₃]
  ring

lemma lineInCubicPerm_last_cond {S : (PureU1 (2 * n.succ.succ+1)).AnomalyFreeLinear}
    (LIC : lineInCubicPerm S) :
    lineInPlaneProp ((S.val (δ!₂ 0)), ((S.val (δ!₁ 0)), (S.val δ!₃))) := by
  obtain ⟨g, f, hfg⟩ := span_basis S
  have h1 := lineInCubicPerm_swap LIC  0 g f hfg
  rw [P_P_P!_accCube' g f hfg] at h1
  simp at h1
  cases h1 <;> rename_i h1
  apply Or.inl
  linear_combination h1
  cases h1 <;> rename_i h1
  apply Or.inr
  apply Or.inl
  linear_combination h1
  apply Or.inr
  apply Or.inr
  linear_combination h1

lemma lineInCubicPerm_last_perm  {S : (PureU1 (2 * n.succ.succ + 1)).AnomalyFreeLinear}
    (LIC : lineInCubicPerm S) : lineInPlaneCond S := by
  refine @Prop_three (2 * n.succ.succ + 1) lineInPlaneProp S (δ!₂ 0) (δ!₁ 0)
    δ!₃ ?_ ?_ ?_ ?_
  simp [Fin.ext_iff, δ!₂, δ!₁]
  simp [Fin.ext_iff, δ!₂, δ!₃]
  simp [Fin.ext_iff, δ!₁, δ!₃]
  intro M
  exact lineInCubicPerm_last_cond (lineInCubicPerm_permute LIC M)

lemma lineInCubicPerm_constAbs  {S : (PureU1 (2 * n.succ.succ + 1)).AnomalyFreeLinear}
    (LIC : lineInCubicPerm S) : constAbs S.val :=
  linesInPlane_constAbs (lineInCubicPerm_last_perm LIC)

theorem  lineInCubicPerm_zero {S : (PureU1 (2 * n.succ.succ + 1)).AnomalyFreeLinear}
    (LIC : lineInCubicPerm S) : S = 0 :=
  ConstAbs.boundary_value_odd S (lineInCubicPerm_constAbs LIC)

end PureU1
