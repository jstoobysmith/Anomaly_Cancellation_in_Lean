/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.PureU1.Basic
import AnomalyCancellationInLean.PureU1.Permutations
import AnomalyCancellationInLean.PureU1.VectorLike
import AnomalyCancellationInLean.PureU1.ConstAbs
import AnomalyCancellationInLean.PureU1.LineInPlaneCond
import AnomalyCancellationInLean.PureU1.Odd.BasisLinear
import Mathlib.Tactic.Polyrith
import Mathlib.RepresentationTheory.Basic

-- https://arxiv.org/pdf/1912.04804.pdf

namespace PureU1
namespace Odd

open BigOperators

variable {n : ℕ}
open VectorLikeOddPlane

/-- The line from P to P! through S is within the cubic. -/
def lineInCubic (S : (PureU1 (2 * n + 1)).LinSols) : Prop :=
  ∀ (g f : Fin n → ℚ)  (_ : S.val = Pa g f) (a b : ℚ) ,
  accCube (2 * n + 1) (a • P g + b • P! f) = 0

lemma lineInCubic_expand {S : (PureU1 (2 * n + 1)).LinSols} (h : lineInCubic S) :
    ∀ (g : Fin n → ℚ) (f : Fin n → ℚ) (_ : S.val = P g + P! f) (a b : ℚ) ,
    3 * a * b * (a * accCubeTriLinSymm (P g, P g, P! f)
    + b * accCubeTriLinSymm (P! f, P! f, P g)) = 0 := by
  intro g f hS a b
  have h1 := h g f hS a b
  change accCubeTriLinSymm.toCubic (a • P g + b • P! f) = 0 at h1
  simp only [TriLinearSymm.toCubic_add] at h1
  simp only [HomogeneousCubic.map_smul,
   accCubeTriLinSymm.map_smul₁, accCubeTriLinSymm.map_smul₂, accCubeTriLinSymm.map_smul₃] at h1
  erw [P_accCube, P!_accCube] at h1
  rw [← h1]
  ring


lemma line_in_cubic_P_P_P! {S : (PureU1 (2 * n + 1)).LinSols} (h : lineInCubic S) :
    ∀ (g : Fin n → ℚ) (f : Fin n → ℚ) (_ : S.val =  P g + P! f),
    accCubeTriLinSymm (P g, P g, P! f) = 0 := by
  intro g f hS
  linear_combination 2 / 3 * (lineInCubic_expand h g f hS 1 1 ) -
     (lineInCubic_expand h g f hS 1 2 ) / 6




/-- The line from P to P! through S is within the cubic for all permutations of S. -/
def lineInCubicPerm (S : (PureU1 (2 * n + 1)).LinSols) : Prop :=
  ∀ (M : (FamilyPermutations (2 * n + 1)).group ),
    lineInCubic ((FamilyPermutations (2 * n + 1)).repAFL M S)

/-- If `lineInCubicPerm S` then `lineInCubic S`.  -/
lemma lineInCubicPerm_self {S : (PureU1 (2 * n + 1)).LinSols} (hS : lineInCubicPerm S) :
    lineInCubic S := hS 1

/-- If `lineInCubicPerm S` then `lineInCubicPerm (M S)` for all permutations `M`. -/
lemma lineInCubicPerm_permute {S : (PureU1 (2 * n + 1)).LinSols}
    (hS : lineInCubicPerm S) (M' : (FamilyPermutations (2 * n + 1)).group) :
    lineInCubicPerm ((FamilyPermutations (2 * n + 1)).repAFL M' S) := by
  rw [lineInCubicPerm]
  intro M
  have ht : (((ACCSystemGroupAction.repAFL (FamilyPermutations (2 * n + 1))) M)
    (((ACCSystemGroupAction.repAFL (FamilyPermutations (2 * n + 1))) M') S))
    = (ACCSystemGroupAction.repAFL (FamilyPermutations (2 * n + 1))) (M * M') S
      := by
    simp [(FamilyPermutations (2 * n.succ)).repAFL.map_mul']
  rw [ht]
  exact hS (M * M')


lemma lineInCubicPerm_swap {S : (PureU1 (2 * n.succ + 1)).LinSols}
    (LIC : lineInCubicPerm S) :
    ∀ (j : Fin n.succ) (g f : Fin n.succ → ℚ) (_ : S.val = Pa g f) ,
      (S.val (δ!₂ j) - S.val (δ!₁ j))
      * accCubeTriLinSymm.toFun (P g, P g, basis!AsCharges j) = 0 := by
  intro j g f h
  let S' :=  (FamilyPermutations (2 * n.succ + 1)).repAFL
    (pairSwap (δ!₁ j) (δ!₂ j)) S
  have hSS' : ((FamilyPermutations (2 * n.succ + 1)).repAFL
    (pairSwap (δ!₁ j) (δ!₂ j))) S = S' := rfl
  obtain ⟨g', f', hall⟩ := span_basis_swap! j hSS' g f h
  have h1 := line_in_cubic_P_P_P! (lineInCubicPerm_self LIC) g f h
  have h2 := line_in_cubic_P_P_P!
    (lineInCubicPerm_self (lineInCubicPerm_permute LIC (pairSwap (δ!₁ j) (δ!₂ j)))) g' f' hall.1
  rw [hall.2.1, hall.2.2] at h2
  rw [accCubeTriLinSymm.map_add₃, h1, accCubeTriLinSymm.map_smul₃] at h2
  simpa using h2

lemma P_P_P!_accCube' {S : (PureU1 (2 * n.succ.succ + 1)).LinSols}
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

lemma lineInCubicPerm_last_cond {S : (PureU1 (2 * n.succ.succ+1)).LinSols}
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

lemma lineInCubicPerm_last_perm  {S : (PureU1 (2 * n.succ.succ + 1)).LinSols}
    (LIC : lineInCubicPerm S) : lineInPlaneCond S := by
  refine @Prop_three (2 * n.succ.succ + 1) lineInPlaneProp S (δ!₂ 0) (δ!₁ 0)
    δ!₃ ?_ ?_ ?_ ?_
  simp [Fin.ext_iff, δ!₂, δ!₁]
  simp [Fin.ext_iff, δ!₂, δ!₃]
  simp [Fin.ext_iff, δ!₁, δ!₃]
  intro M
  exact lineInCubicPerm_last_cond (lineInCubicPerm_permute LIC M)

lemma lineInCubicPerm_constAbs  {S : (PureU1 (2 * n.succ.succ + 1)).LinSols}
    (LIC : lineInCubicPerm S) : constAbs S.val :=
  linesInPlane_constAbs (lineInCubicPerm_last_perm LIC)

theorem  lineInCubicPerm_zero {S : (PureU1 (2 * n.succ.succ + 1)).LinSols}
    (LIC : lineInCubicPerm S) : S = 0 :=
  ConstAbs.boundary_value_odd S (lineInCubicPerm_constAbs LIC)

end Odd
end PureU1
