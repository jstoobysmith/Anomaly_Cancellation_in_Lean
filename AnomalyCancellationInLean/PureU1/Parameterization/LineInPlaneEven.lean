/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.PureU1.Basic
import AnomalyCancellationInLean.PureU1.ConstAbs
import AnomalyCancellationInLean.PureU1.Parameterization.EvenPlanes
import AnomalyCancellationInLean.PureU1.Parameterization.LineInPlaneCond
import AnomalyCancellationInLean.PureU1.Permutations
import Mathlib.RepresentationTheory.Basic
import Mathlib.Tactic.Polyrith

-- https://arxiv.org/pdf/1912.04804.pdf

namespace PureU1

open BigOperators

variable {n : ℕ}
open VectorLikeEvenPlane

/-- A line in the cubic. -/
def lineInCubic (S : (PureU1 (2 * n.succ)).AnomalyFreeLinear) : Prop :=
  ∀ (g : Fin n.succ → ℚ) (f : Fin n → ℚ) (_ : S.val = Pa g f) (a b : ℚ) ,
  (PureU1.accCube (2 * n.succ)).toFun (a • P g + b • P! f) = 0

/--
 This lemma states that for a given `S` of type `(PureU1 (2 * n.succ)).AnomalyFreeLinear` and
 a proof `h` that the line through `S` lies on a cubic curve,
 for any functions `g : Fin n.succ → ℚ` and `f : Fin n → ℚ`, if `S.val = P g + P! f`,
 then `accCubeTriLinSymm.toFun (P g, P g, P! f) = 0`.
-/
lemma line_in_cubic_P_P_P! {S : (PureU1 (2 * n.succ)).AnomalyFreeLinear} (h : lineInCubic S) :
  ∀ (g : Fin n.succ → ℚ) (f : Fin n → ℚ) (_ : S.val =  P g + P! f),
  accCubeTriLinSymm.toFun (P g, P g, P! f) = 0 := by
  intro g f hS
  rw [lineInCubic] at h
  let h := h g f hS
  rw [accCubetoCubic_add
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


def lineInCubicPerm (S : (PureU1 (2 * n.succ)).AnomalyFreeLinear) : Prop :=
  ∀ (M : (FamilyPermutations (2 * n.succ)).group ),repAFL
  lineInCubic ((FamilyPermutations (2 * n.succ)).repAnomalyFreeLinear M S)

/-- If `lineInCubicPerm S` then `lineInCubic S`.  -/
lemma lineInCubicPerm_self {S : (PureU1 (2 * n.succ)).AnomalyFreeLinear}
    (hS : lineInCubicPerm S) : lineInCubic S := hS 1

/-- If `lineInCubicPerm S` then `lineInCubicPerm (M S)` for all permutations `M`. -/
lemma lineInCubicPerm_permute {S : (PureU1 (2 * n.succ)).AnomalyFreeLinear}
    (hS : lineInCubicPerm S) (M' : (FamilyPermutations repAFL :
    lineInCubicPerm ((FamilyPermutations (2 * n.succ)).repAnomalyFreeLinear M' S) := by
  rw [lineInCubicPerm]
  intro MrepAFL
  have repAFLeeLinear (FamilyPermutations (2 * Nat.succ n))) M)
    (((repAFL (FamilyPermutations (2 * Nat.succ n))) M') S))
    = (ACCSystemGroupAction.repAnomalyFreeLinear (FamilyPermutations (2 * Nat.succ n))) (M * M') S
      := byrepAFL
    simp [(FamilyPermutations (2 * n.succ)).repAnomalyFreeLinear.map_mul']
  rw [ht]
  exact hS (M * M')

lemma lineInCubicPerm_swap {S : (PureU1 (2 * n.succ)).AnomalyFreeLinear}
    (LIC : lineInCubicPerm S) :
    ∀ (j : Fin n) (g : Fin n.succ → ℚ) (f : Fin n → ℚ) (_ : S.val = Pa g f) ,
      (S.val (δ!₂ j) - S.val (δ!₁ j))
      * accCubeTriLinSymm.toFun (P g, P g, basis!AsCharges j) = 0 := by
  intro j g f hrepAFL
  let S' :=  (FamilyPermutations (2 * n.succ)).repAnomalyFreeLinear
    (pairSwap (δ!₁ j) (δ!₂ j)) SrepAFL
  have hSS' : ((FamilyPermutations (2 * n.succ)).repAnomalyFreeLinear
    (pairSwap (δ!₁ j) (δ!₂ j))) S = S' := rfl
  obtain ⟨g', f', hall⟩ := span_basis_swap! j hSS' g f h
  have h1 := line_in_cubic_P_P_P! (lineInCubicPerm_self LIC) g f h
  have h2 := line_in_cubic_P_P_P!
    (lineInCubicPerm_self (lineInCubicPerm_permute LIC (pairSwap (δ!₁ j) (δ!₂ j)))) g' f' hall.1
  rw [hall.2.1, hall.2.2] at h2
  rw [accCubeTriLinSymm.map_add₃, h1, accCubeTriLinSymm.map_smul₃] at h2
  simpa using h2

lemma P_P_P!_accCube' {S : (PureU1 (2 * n.succ.succ )).AnomalyFreeLinear}
     (f : Fin n.succ.succ → ℚ) (g : Fin n.succ → ℚ) (hS : S.val = Pa f g) :
    accCubeTriLinSymm.toFun (P f, P f, basis!AsCharges  (Fin.last n)) =
    - (S.val (δ!₂ (Fin.last n)) + S.val (δ!₁ (Fin.last n))) * (2 * S.val δ!₄ +
     S.val (δ!₂ (Fin.last n))  + S.val (δ!₁ (Fin.last n))) := by
  rw [P_P_P!_accCube f  (Fin.last n)]
  have h1 := Pa_δ!₄ f g
  have h2 := Pa_δ!₁ f g (Fin.last n)
  have h3 := Pa_δ!₂ f g (Fin.last n)
  simp at h1 h2 h3
  have hl : f (Fin.succ  (Fin.last (n ))) = - Pa f g δ!₄ := by
    simp_all only [PureU1_charges, Fin.succ_last, neg_neg]
  erw [hl] at h2
  have hg : g (Fin.last n)  = Pa f g (δ!₁ (Fin.last n)) + Pa f g δ!₄ := by
    linear_combination -(1 * h2)
  have hll : f (Fin.castSucc  (Fin.last (n ))) =
      - (Pa f g (δ!₂ (Fin.last n))  + Pa f g (δ!₁ (Fin.last n)) + Pa f g δ!₄) := by
    linear_combination h3 - 1 * hg
  rw [← hS] at hl hll
  rw [hl, hll]
  ring

lemma lineInCubicPerm_last_cond {S : (PureU1 (2 * n.succ.succ)).AnomalyFreeLinear}
    (LIC : lineInCubicPerm S) :
    lineInPlaneProp
    ((S.val (δ!₂ (Fin.last n))), ((S.val (δ!₁ (Fin.last n))), (S.val δ!₄))) := by
  obtain ⟨g, f, hfg⟩ := span_basis S
  have h1 := lineInCubicPerm_swap LIC (Fin.last n) g f hfg
  rw [P_P_P!_accCube' g f hfg] at h1
  simp at h1
  cases h1 <;> rename_i h1
  apply Or.inl
  linear_combination h1
  cases h1 <;> rename_i h1
  apply Or.inr
  apply Or.inl
  linear_combination -(1 * h1)
  apply Or.inr
  apply Or.inr
  exact h1

lemma lineInCubicPerm_last_perm  {S : (PureU1 (2 * n.succ.succ)).AnomalyFreeLinear}
    (LIC : lineInCubicPerm S) : lineInPlaneCond S := by
  refine @Prop_three (2 * n.succ.succ) lineInPlaneProp S (δ!₂ (Fin.last n)) (δ!₁ (Fin.last n))
    δ!₄ ?_ ?_ ?_ ?_
  simp [Fin.ext_iff, δ!₂, δ!₁]
  simp [Fin.ext_iff, δ!₂, δ!₄]
  simp [Fin.ext_iff, δ!₁, δ!₄]
  omega
  intro M
  exact lineInCubicPerm_last_cond (lineInCubicPerm_permute LIC M)

lemma lineInCubicPerm_constAbs  {S : (PureU1 (2 * n.succ.succ)).AnomalyFree}
    (LIC : lineInCubicPerm S.1.1) : constAbs S.val :=
  linesInPlane_constAbs_AF S (lineInCubicPerm_last_perm LIC)

theorem  lineInCubicPerm_vectorLike  {S : (PureU1 (2 * n.succ.succ)).AnomalyFree}
    (LIC : lineInCubicPerm S.1.1) : vectorLikeEven S.val :=
  ConstAbs.boundary_value_even S.1.1 (lineInCubicPerm_constAbs LIC)

theorem lineInCubicPerm_in_plane  (S : (PureU1 (2 * n.succ.succ)).AnomalyFree)
    (LIC : lineInCubicPerm S.1.1) : ∃ (M : (FamilyPermutations (2 * n.succ.succ)).group),
    (FamilyPermutations (2 * n.succ.succ)).repAnrepAFL1.1
    ∈ Submodule.span ℚ (Set.range basis) :=
  vectorLikeEven_in_span S.1.1 (lineInCubicPerm_vectorLike LIC)



end PureU1
