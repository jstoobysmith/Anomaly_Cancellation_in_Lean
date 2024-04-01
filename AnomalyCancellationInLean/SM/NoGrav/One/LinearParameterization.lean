/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.SM.Basic
import AnomalyCancellationInLean.SM.NoGrav.Basic
universe v u

-- based on https://arxiv.org/abs/1907.00514

namespace SM
namespace SMNoGrav
namespace One

open SMCharges
open SMACCs
open BigOperators

structure linearParameters where
  Q' : ℚ
  Y : ℚ
  E' : ℚ

namespace linearParameters

@[ext]
lemma ext {S T : linearParameters} (hQ : S.Q' = T.Q') (hY : S.Y = T.Y) (hE : S.E' = T.E')  : S = T := by
  cases' S
  simp_all only

@[simp]
def asCharges (S : linearParameters) : (SMNoGrav 1).charges := fun i =>
  match i with
  | 0 => S.Q'
  | 1 => S.Y - S.Q'
  | 2 => - (S.Y + S.Q')
  | 3 => - 3 * S.Q'
  | 4 => S.E'

lemma speciesVal (S : linearParameters) : (toSpecies i) S.asCharges 0 = S.asCharges i := by
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl
  | 4 => rfl

def asLinear (S : linearParameters) : (SMNoGrav 1).AnomalyFreeLinear :=
  chargeToLinear S.asCharges (by
    simp
    erw [speciesVal, speciesVal]
    simp)
    (by
    simp
    repeat erw [speciesVal]
    simp
    ring)

lemma asLinear_val (S : linearParameters) : S.asLinear.val = S.asCharges := by
  rfl

@[simp]
lemma cubic (S : linearParameters) :
    accCube (S.asCharges) = - 54 * S.Q'^3 - 18 * S.Q' * S.Y ^ 2 + S.E'^3 := by
  simp
  erw [← TriLinearSymm.toFun_eq_coe]
  rw [cubeTriLin]
  simp
  repeat erw [speciesVal]
  simp
  ring

lemma cubic_zero_Q'_zero (S : linearParameters) (hc : accCube (S.asCharges) = 0)
    (h : S.Q' = 0) : S.E' = 0 := by
  rw [cubic, h] at hc
  simp at hc
  exact hc

lemma cubic_zero_E'_zero (S : linearParameters) (hc : accCube (S.asCharges) = 0)
    (h : S.E' = 0) : S.Q' = 0 := by
  rw [cubic, h] at hc
  simp at hc
  have h1 : -(54 * S.Q' ^ 3) - 18 * S.Q' * S.Y ^ 2 = - 18 * (3 * S.Q' ^ 2 + S.Y ^ 2) * S.Q' := by
    ring
  rw [h1] at hc
  simp at hc
  cases' hc with hc hc
  have h2 := (add_eq_zero_iff' (by nlinarith) (by nlinarith)).mp hc
  simp at h2
  exact h2.1
  exact hc

def bijection : linearParameters ≃ (SMNoGrav 1).AnomalyFreeLinear where
  toFun S := S.asLinear
  invFun S := ⟨SMCharges.Q S.val 0, (SMCharges.U S.val 0 - SMCharges.D S.val 0)/2 ,
     SMCharges.E S.val 0⟩
  left_inv S := by
    apply linearParameters.ext
    simp
    repeat erw [speciesVal]
    simp
    repeat erw [speciesVal]
    simp
    repeat erw [speciesVal]
    simp
    ring
    simp
    repeat erw [speciesVal]
    simp
  right_inv S := by
    simp
    apply ACCSystemLinear.AnomalyFreeLinear.ext
    rw [charges_eq_toSpecies_eq]
    intro i
    rw [asLinear_val]
    funext j
    have hj : j = 0 := by
      simp only [Fin.isValue]
      ext
      simp
    subst hj
    erw [speciesVal]
    have h1 := SU3Sol S
    simp at h1
    have h2 := SU2Sol S
    simp at h2
    match i with
    | 0 => rfl
    | 1 =>
      field_simp
      linear_combination -(1 * h1)
    | 2 =>
      field_simp
      linear_combination -(1 * h1)
    | 3 =>
      field_simp
      linear_combination -(1 * h2)
    | 4 => rfl

def bijectionQEZero : {S : linearParameters // S.Q' ≠ 0 ∧ S.E' ≠ 0} ≃
  {S : (SMNoGrav 1).AnomalyFreeLinear // Q S.val 0 ≠ 0 ∧ E S.val 0 ≠ 0} where
  toFun S := ⟨bijection S, S.2⟩
  invFun S := ⟨bijection.symm S, S.2⟩
  left_inv S := by
    apply Subtype.ext
    exact bijection.left_inv S.1
  right_inv S := by
    apply Subtype.ext
    exact bijection.right_inv S.1

lemma grav (S : linearParameters) :
    accGrav S.asCharges = 0 ↔ S.E' = 6 * S.Q' := by
  rw [accGrav]
  simp
  repeat erw [speciesVal]
  simp
  ring_nf
  rw [add_comm, add_eq_zero_iff_eq_neg]
  simp

end linearParameters


structure linearParametersQENeqZero where
  x : ℚ
  v : ℚ
  w : ℚ
  hx : x ≠ 0
  hvw : v + w ≠ 0

namespace linearParametersQENeqZero

@[ext]
lemma ext {S T : linearParametersQENeqZero} (hx : S.x = T.x) (hv : S.v = T.v)
    (hw : S.w = T.w)  : S = T := by
  cases' S
  simp_all only

@[simps!]
def toLinearParameters (S : linearParametersQENeqZero) :
    {S : linearParameters // S.Q' ≠  0 ∧ S.E' ≠ 0} :=
  ⟨⟨S.x,   3 * S.x * (S.v - S.w) / (S.v + S.w),  - 6 * S.x  / (S.v + S.w)⟩,
    by
      apply And.intro S.hx
      simp
      rw [not_or]
      exact And.intro S.hx S.hvw⟩

-- Need to change namespace of this
@[simps!]
def tolinearParametersQNeqZero (S : {S : linearParameters //  S.Q' ≠  0 ∧ S.E' ≠ 0}) :
    linearParametersQENeqZero :=
  ⟨S.1.Q', - (3 * S.1.Q' + S.1.Y) / S.1.E', - (3 * S.1.Q' - S.1.Y)/ S.1.E',  S.2.1,
    by
      simp
      field_simp
      rw [not_or]
      ring_nf
      simp
      exact S.2⟩

@[simps!]
def bijectionLinearParameters :
    linearParametersQENeqZero ≃ {S : linearParameters //  S.Q' ≠ 0 ∧ S.E' ≠ 0} where
  toFun := toLinearParameters
  invFun := tolinearParametersQNeqZero
  left_inv S := by
    have hvw := S.hvw
    have hQ := S.hx
    apply linearParametersQENeqZero.ext
    simp
    field_simp
    ring
    simp
    field_simp
    ring
  right_inv S := by
    apply Subtype.ext
    have hQ := S.2.1
    have hE := S.2.2
    apply linearParameters.ext
    simp
    field_simp
    ring_nf
    field_simp [hQ, hE]
    ring
    field_simp
    ring_nf
    field_simp [hQ, hE]
    ring

def bijection : linearParametersQENeqZero ≃
    {S : (SMNoGrav 1).AnomalyFreeLinear // Q S.val 0 ≠ 0 ∧ E S.val 0 ≠ 0} :=
  bijectionLinearParameters.trans (linearParameters.bijectionQEZero)

lemma cubic (S : linearParametersQENeqZero) :
    accCube (bijection S).1.val = 0 ↔ S.v ^ 3 + S.w ^ 3 = -1 := by
  erw [linearParameters.cubic]
  simp
  have hvw := S.hvw
  have hQ := S.hx
  field_simp
  have h1 : (-(54 * S.x ^ 3 * (S.v + S.w) ^ 2) - 18 * S.x * (3 * S.x * (S.v - S.w)) ^ 2) *
      (S.v + S.w) ^ 3 + (-(6 * S.x)) ^ 3 * (S.v + S.w) ^ 2 =
      - 216 * S.x ^3 * (S.v ^3 + S.w ^3 +1) * (S.v + S.w) ^ 2 := by
    ring
  rw [h1]
  simp_all
  rw [add_eq_zero_iff_eq_neg]

lemma FLTThree : FermatLastTheoremWith ℚ 3 := by sorry

lemma cubic_v_or_w_zero (S : linearParametersQENeqZero) (h : accCube (bijection S).1.val = 0) :
    S.v = 0 ∨ S.w = 0 := by
  rw [S.cubic] at h
  have h1 : (-1)^3 = (-1 : ℚ):= by rfl
  rw [← h1] at h
  by_contra hn
  simp [not_or] at hn
  have h2 := FLTThree S.v S.w (-1) hn.1 hn.2 (by simp)
  simp_all

lemma cubic_v_zero (S : linearParametersQENeqZero) (h : accCube (bijection S).1.val = 0)
    (hv : S.v = 0 ) : S.w = -1 := by
  rw [S.cubic, hv] at h
  simp at h
  have h' : (S.w + 1) * (1 * S.w * S.w + (-1) * S.w + 1) = 0 := by
    ring_nf
    rw [add_comm]
    exact add_eq_zero_iff_eq_neg.mpr h
  have h'' : (1 * S.w * S.w + (-1) * S.w + 1)  ≠ 0 := by
    refine quadratic_ne_zero_of_discrim_ne_sq ?_ S.w
    intro s
    by_contra hn
    have h : s ^ 2 < 0 := by
      rw [← hn]
      simp [discrim]
    nlinarith
  simp_all
  linear_combination h'

lemma cube_w_zero (S : linearParametersQENeqZero) (h : accCube (bijection S).1.val = 0)
    (hw : S.w = 0 ) : S.v = -1 := by
  rw [S.cubic, hw] at h
  simp at h
  have h' : (S.v + 1) * (1 * S.v * S.v + (-1) * S.v + 1) = 0 := by
    ring_nf
    rw [add_comm]
    exact add_eq_zero_iff_eq_neg.mpr h
  have h'' : (1 * S.v * S.v + (-1) * S.v + 1)  ≠ 0 := by
    refine quadratic_ne_zero_of_discrim_ne_sq ?_ S.v
    intro s
    by_contra hn
    have h : s ^ 2 < 0 := by
      rw [← hn]
      simp [discrim]
    nlinarith
  simp_all
  linear_combination h'

lemma cube_w_v (S : linearParametersQENeqZero) (h : accCube (bijection S).1.val = 0) :
    (S.v = -1 ∧ S.w = 0) ∨ (S.v = 0 ∧ S.w = -1) := by
  have h' := cubic_v_or_w_zero S h
  cases' h' with hx hx
  simp [hx]
  exact cubic_v_zero S h hx
  simp [hx]
  exact cube_w_zero S h hx

lemma grav (S : linearParametersQENeqZero) : accGrav (bijection S).1.val = 0 ↔ S.v + S.w = -1 := by
  erw [linearParameters.grav]
  have hvw := S.hvw
  have hQ := S.hx
  field_simp
  apply Iff.intro
  intro h
  apply (mul_right_inj' hQ).mp
  linear_combination -1 * h / 6
  intro h
  rw [h]
  ring

lemma grav_of_cubic (S : linearParametersQENeqZero) (h : accCube (bijection S).1.val = 0) :
    accGrav (bijection S).1.val = 0 := by
  rw [grav]
  have h' := cube_w_v S h
  cases' h' with h h
  rw [h.1, h.2]
  simp
  rw [h.1, h.2]
  simp


end linearParametersQENeqZero


end One
end SMNoGrav
end SM
