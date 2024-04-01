/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.SM.Basic
import AnomalyCancellationInLean.SM.NoGrav.Basic
import AnomalyCancellationInLean.SM.NoGrav.One.LinearParameterization
universe v u

-- based on https://arxiv.org/abs/1907.00514

namespace SM
namespace SMNoGrav
namespace One

open SMCharges
open SMACCs
open BigOperators


lemma E_zero_iff_Q_zero {S : (SMNoGrav 1).AnomalyFree} : Q S.val 0 = 0 ↔ E S.val 0 = 0 := by
  let S' := linearParameters.bijection.symm S.1.1
  have hC := cubeSol S
  have hS' := congrArg (fun S => S.val) (linearParameters.bijection.right_inv S.1.1)
  change  S'.asCharges = S.val at hS'
  rw [← hS'] at hC
  apply Iff.intro
  intro hQ
  exact S'.cubic_zero_Q'_zero hC hQ
  intro hE
  exact S'.cubic_zero_E'_zero hC hE



lemma accGrav_Q_zero {S : (SMNoGrav 1).AnomalyFree} (hQ : Q S.val 0 = 0) : accGrav S.val = 0 := by
  rw [accGrav]
  simp
  erw [hQ, E_zero_iff_Q_zero.mp hQ]
  have h1 := SU2Sol S.1.1
  have h2 := SU3Sol S.1.1
  simp at h1 h2
  erw [hQ] at h1 h2
  simp_all
  linear_combination 3 * h2

lemma accGrav_Q_neq_zero {S : (SMNoGrav 1).AnomalyFree} (hQ : Q S.val 0 ≠ 0) :
    accGrav S.val = 0 := by
  have hE := E_zero_iff_Q_zero.mpr.mt hQ
  let S' := linearParametersQENeqZero.bijection.symm ⟨S.1.1, And.intro hQ hE⟩
  have hC := cubeSol S
  have hS' := congrArg (fun S => S.val.val)
    (linearParametersQENeqZero.bijection.right_inv ⟨S.1.1, And.intro hQ hE⟩)
  change  _ = S.val at hS'
  rw [← hS'] at hC
  rw [← hS']
  exact S'.grav_of_cubic hC

/-- The result of https://arxiv.org/abs/1907.00514. -/
theorem accGravSatisfied {S : (SMNoGrav 1).AnomalyFree} : accGrav S.val = 0 := by
  by_cases hQ : Q S.val 0 = 0
  exact accGrav_Q_zero hQ
  exact accGrav_Q_neq_zero hQ


end One
end SMNoGrav
end SM
