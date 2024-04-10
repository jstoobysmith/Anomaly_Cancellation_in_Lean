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
import AnomalyCancellationInLean.PureU1.Odd.LineInCubic
import Mathlib.Tactic.Polyrith
import Mathlib.RepresentationTheory.Basic

-- https://arxiv.org/pdf/1912.04804.pdf

namespace PureU1
namespace Odd
open BigOperators

variable {n : ℕ}
open VectorLikeOddPlane

def parameterizationAsLinear (g f : Fin n → ℚ)  (a : ℚ) :
  (PureU1 (2 * n + 1)).LinSols :=
  a • ((accCubeTriLinSymm (P! f, P! f, P g)) • P' g +
  (- accCubeTriLinSymm (P g, P g, P! f)) • P!' f)

lemma parameterizationAsLinear_val (g f : Fin n → ℚ) (a : ℚ) :
  (parameterizationAsLinear g f a).val =
    a • ((accCubeTriLinSymm (P! f, P! f, P g)) • P g +
    (- accCubeTriLinSymm (P g, P g, P! f)) • P! f) := by
  rw [parameterizationAsLinear]
  change a • (_ • (P' g).val + _ • (P!' f).val) = _
  rw [P'_val, P!'_val]

lemma parameterizationCharge_cube (g f : Fin n → ℚ)  (a : ℚ):
    (accCube (2 * n + 1)) (parameterizationAsLinear g f a).val = 0 := by
  change accCubeTriLinSymm.toCubic _ = 0
  rw [parameterizationAsLinear_val]
  rw [HomogeneousCubic.map_smul]
  rw [TriLinearSymm.toCubic_add]
  rw [HomogeneousCubic.map_smul, HomogeneousCubic.map_smul]
  erw [P_accCube g, P!_accCube f]
  rw [accCubeTriLinSymm.map_smul₁, accCubeTriLinSymm.map_smul₂,
   accCubeTriLinSymm.map_smul₃, accCubeTriLinSymm.map_smul₁, accCubeTriLinSymm.map_smul₂,
   accCubeTriLinSymm.map_smul₃]
  ring

def parameterization (g f : Fin n → ℚ) (a : ℚ) :
    (PureU1 (2 * n + 1)).Sols :=
  ⟨⟨parameterizationAsLinear g f a, by intro i; simp at i; exact Fin.elim0 i⟩,
  parameterizationCharge_cube g f a⟩

lemma anomalyFree_param {S : (PureU1 (2 * n + 1)).Sols}
    (g f : Fin n → ℚ)  (hS : S.val = P g + P! f) :
    accCubeTriLinSymm (P g, P g, P! f) =
    - accCubeTriLinSymm (P! f, P! f, P g) := by
  have hC := S.cubicSol
  rw [hS] at hC
  change (accCube (2 * n + 1)) (P g + P! f) = 0 at hC
  erw [TriLinearSymm.toCubic_add] at hC
  erw [P_accCube] at hC
  erw [P!_accCube] at hC
  linear_combination hC / 3

def genericCase (S : (PureU1 (2 * n.succ + 1)).Sols) : Prop :=
  ∀ (g f : Fin n.succ → ℚ)  (_ : S.val = P g + P! f) ,
  accCubeTriLinSymm (P g, P g, P! f) ≠  0

lemma genericCase_exists (S : (PureU1 (2 * n.succ + 1)).Sols)
    (hs : ∃ (g f : Fin n.succ → ℚ), S.val = P g + P! f ∧
    accCubeTriLinSymm (P g, P g, P! f) ≠  0) : genericCase S := by
  intro g f hS hC
  obtain ⟨g', f', hS', hC'⟩ := hs
  rw [hS] at hS'
  erw [Pa_eq] at hS'
  rw [hS'.1, hS'.2] at hC
  exact hC' hC

def specialCase  (S : (PureU1 (2 * n.succ + 1)).Sols) : Prop :=
  ∀ (g f : Fin n.succ → ℚ) (_ : S.val = P g + P! f) ,
  accCubeTriLinSymm (P g, P g, P! f) = 0

lemma specialCase_exists (S : (PureU1 (2 * n.succ + 1)).Sols)
    (hs : ∃ (g f : Fin n.succ → ℚ), S.val = P g + P! f ∧
    accCubeTriLinSymm (P g, P g, P! f) =  0) : specialCase S := by
  intro g f hS
  obtain ⟨g', f', hS', hC'⟩ := hs
  rw [hS] at hS'
  erw [Pa_eq] at hS'
  rw [hS'.1, hS'.2]
  exact hC'

lemma generic_or_special (S : (PureU1 (2 * n.succ + 1)).Sols) :
    genericCase S ∨ specialCase S := by
  obtain ⟨g, f, h⟩ := span_basis S.1.1
  have h1 :  accCubeTriLinSymm (P g, P g, P! f) ≠  0 ∨
     accCubeTriLinSymm (P g, P g, P! f) = 0 := by
    exact ne_or_eq _ _
  cases h1 <;> rename_i h1
  exact Or.inl (genericCase_exists S ⟨g, f, h, h1⟩)
  exact Or.inr (specialCase_exists S ⟨g, f, h, h1⟩)

theorem generic_case {S : (PureU1 (2 * n.succ + 1)).Sols} (h : genericCase S) :
      ∃ g f a,  S = parameterization g f a := by
  obtain ⟨g, f, hS⟩ := span_basis S.1.1
  use g, f, (accCubeTriLinSymm (P! f, P! f, P g))⁻¹
  rw [parameterization]
  apply ACCSystem.Sols.ext
  rw [parameterizationAsLinear_val]
  change S.val = _ • ( _ • P g + _• P! f)
  rw [anomalyFree_param _ _ hS]
  rw [neg_neg, ← smul_add, smul_smul, inv_mul_cancel, one_smul]
  exact hS
  have h := h g f hS
  rw [anomalyFree_param _ _ hS] at h
  simp at h
  exact h


lemma special_case_lineInCubic {S : (PureU1 (2 * n.succ + 1)).Sols}
    (h : specialCase S) :
      lineInCubic S.1.1 := by
  intro g f hS a b
  erw [TriLinearSymm.toCubic_add]
  rw [HomogeneousCubic.map_smul, HomogeneousCubic.map_smul]
  erw [P_accCube]
  erw [P!_accCube]
  have h := h g f hS
  rw [accCubeTriLinSymm.map_smul₁, accCubeTriLinSymm.map_smul₂,
   accCubeTriLinSymm.map_smul₃, accCubeTriLinSymm.map_smul₁, accCubeTriLinSymm.map_smul₂,
   accCubeTriLinSymm.map_smul₃]
  rw [h]
  rw [anomalyFree_param _ _ hS] at h
  simp at h
  change accCubeTriLinSymm (P! f, P! f, P g) = 0 at h
  erw [h]
  simp

lemma special_case_lineInCubic_perm {S : (PureU1 (2 * n.succ + 1)).Sols}
    (h : ∀ (M : (FamilyPermutations (2 * n.succ + 1)).group),
    specialCase ((FamilyPermutations (2 * n.succ + 1)).solAction.toFun S M)) :
    lineInCubicPerm S.1.1 := by
  intro M
  have hM := special_case_lineInCubic (h M)
  exact hM

theorem special_case {S : (PureU1 (2 * n.succ.succ + 1)).Sols}
    (h : ∀ (M : (FamilyPermutations (2 * n.succ.succ + 1)).group),
    specialCase ((FamilyPermutations (2 * n.succ.succ + 1)).solAction.toFun S M)) :
    S.1.1 = 0 := by
  have ht :=  special_case_lineInCubic_perm h
  exact lineInCubicPerm_zero ht
end Odd
end PureU1
