/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.StandardModel.Basic
import Mathlib.Tactic.Polyrith
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.NumberTheory.FLT.Basic
import Mathlib.Algebra.QuadraticDiscriminant

lemma FLTThree : FermatLastTheoremWith ℚ 3 := by sorry

namespace SMOneFamily

structure AnomalyFreeLinearNotGrav where
  val : Charge
  SU2 : accSU2 val = 0
  SU3 : accSU3 val = 0

@[ext]
lemma AnomalyFreeLinearNotGrav.ext {S T : AnomalyFreeLinearNotGrav} (h : S.val = T.val) :
    S = T := by
  cases' S
  simp_all only

structure AnomalyFreeNotGrav where
  val : AnomalyFreeLinearNotGrav
  cube : accCube val.val = 0

@[ext]
lemma AnomalyFreeNotGrav.ext {S T : AnomalyFreeNotGrav} (h : S.val.val = T.val.val) :
    S = T := by
  have h1 : S.val = T.val := AnomalyFreeLinearNotGrav.ext h
  cases' S
  simp_all only


namespace LohitsiriTong


structure parameters where
  Q : ℚ
  Y : ℚ
  E : ℚ

@[ext]
lemma parameters.ext {S T : parameters}
  (hQ : S.Q = T.Q) (hY : S.Y = T.Y) (hE : S.E = T.E)  : S = T := by
  cases' S
  simp_all only

@[simps!]
def parameterization : parameters ≃ SMOneFamily.AnomalyFreeLinearNotGrav where
  toFun S :=
    ⟨⟨S.Q, (S.Y - S.Q), -(S.Y + S.Q), -3*S.Q, S.E⟩ , by simp, by simp; ring⟩
  invFun S :=
    ⟨S.1.Q, (S.1.U - S.1.D)/2 , S.1.E⟩
  left_inv S := by
    apply parameters.ext
    rfl
    ring
    ring
  right_inv S := by
    have hS1 := S.SU2
    have hS2 := S.SU3
    simp_all
    have ht : S.val.U = - S.val.D - 2 * S.val.Q := by
        linear_combination hS2
    apply AnomalyFreeLinearNotGrav.ext
    apply Charge.ext
    · rfl
    · simp
      rw [ht]
      ring
    · simp
      rw [ht]
      ring
    · linear_combination -(1 * hS1)
    · rfl



@[simp]
def accCubicParameters (S : parameters) : ℚ := - 54 * S.Q^3 - 18 * S.Q * S.Y ^ 2 + S.E^3

structure parametersCubic where
  val : parameters
  cube : accCubicParameters val = 0


lemma parametersCubic.ext {S T : parametersCubic} (h : S.val = T.val ) :
    S = T := by
  cases' S
  simp_all only

lemma cubic_parameters (S : parameters) :
    SMOneFamily.accCube (parameterization.toFun S).val = accCubicParameters S := by
  simp [parameterization]
  ring

@[simps!]
def parametersCubicEquiv : parametersCubic ≃ AnomalyFreeNotGrav where
  toFun S := ⟨parameterization.toFun S.val, by
    rw [cubic_parameters]
    exact S.cube
    ⟩
  invFun S := ⟨parameterization.invFun S.val, by
   rw [← cubic_parameters]
   erw [parameterization.right_inv]
   exact S.cube
   ⟩
  left_inv S := by
    apply parametersCubic.ext
    simp
  right_inv S := by
    apply AnomalyFreeNotGrav.ext
    simp


structure parametersCubicQNEZero where
  val : parametersCubic
  Q : val.val.Q ≠  0

lemma parametersCubicQNEZero.ext {S T : parametersCubicQNEZero} (h : S.val.val = T.val.val ) :
    S = T := by
  have h1 : S.val = T.val := parametersCubic.ext h
  cases' S
  simp_all only


lemma accCubicParameters_Q_zero  (S : parameters) (hQ : S.Q = 0) :
    accCubicParameters S = 0 ↔ S.E = 0 := by
  apply Iff.intro
  · intro h
    simp at h
    rw [hQ] at h
    simpa using h
  · intro h
    simp
    rw [hQ, h]
    simp



lemma accCubicParameters_E_zero  (S : parameters) (hE : S.E = 0) :
    accCubicParameters S = 0 ↔ S.Q = 0 := by
  apply Iff.intro
  · intro h
    simp at h
    rw [hE] at h
    simp at h
    have h1 : 18 * S.Q * (3 * S.Q ^ 2 + S.Y ^ 2) = 0 := by
      linarith [h]
    by_contra hQ
    have h2 := or_iff_not_imp_left.mp (mul_eq_zero.mp h1) (by
      intro h;
      have hn : S.Q = 0 := by
        linarith
      exact hQ hn)
    have hQ : 3 * S.Q ^ 2 > 0 := by
      apply mul_pos
      rfl
      exact pow_two_pos_of_ne_zero S.Q hQ
    have hY : S.Y^2 ≥ 0 := by
      exact sq_nonneg S.Y
    linarith
  · intro h
    simp
    rw [hE, h]
    simp



structure parametersFLT where
  Q : ℚ
  v : ℚ
  w : ℚ
  hQ : Q ≠ 0
  hvw : v + w ≠ 0
  hcube : v^3 + w^3 = -1


lemma parametersFLT_v_zero (S : parametersFLT)  (hv : S.v = 0 ) :  S.w = -1 := by
  have hS := S.hcube
  rw [hv] at hS
  simp at hS
  have h21 : (S.w)^3 + 1 = 0 := eq_neg_iff_add_eq_zero.mp hS
  have h22 : (S.w)^3 + 1  = (S.w +1) * (1 * S.w * S.w + (-1) * S.w + 1)  := by
    ring
  rw [h22] at h21
  simp at h21
  rcases h21 with h | h
  exact eq_neg_iff_add_eq_zero.mpr h
  have ht : ∀ (x : ℚ), (1 * x * x + (- 1) * x +1 ) ≠ 0 := by
    intro x
    refine quadratic_ne_zero_of_discrim_ne_sq ?_ x
    simp [discrim]
    intro s
    ring_nf
    by_contra h1
    have hs : 0 ≤ s^2 :=  sq_nonneg s
    rw [← h1] at hs
    simp at hs
    exact (not_le.mpr (by rfl )) hs
  have htS := ht S.w
  field_simp at htS
  exact (htS h).elim

lemma parametersFLT_w_zero (S : parametersFLT)  (hw : S.w = 0 ) :  S.v = -1 := by
  have hS := S.hcube
  rw [hw] at hS
  simp at hS
  have h21 : (S.v)^3 + 1 = 0 := eq_neg_iff_add_eq_zero.mp hS
  have h22 : (S.v)^3 + 1  = (S.v +1) * (1 * S.v * S.v + (-1) * S.v + 1)  := by
    ring
  rw [h22] at h21
  simp at h21
  rcases h21 with h | h
  exact eq_neg_iff_add_eq_zero.mpr h
  have ht : ∀ (x : ℚ), (1 * x * x + (- 1) * x +1 ) ≠ 0 := by
    intro x
    refine quadratic_ne_zero_of_discrim_ne_sq ?_ x
    simp [discrim]
    intro s
    ring_nf
    by_contra h1
    have hs : 0 ≤ s^2 :=  sq_nonneg s
    rw [← h1] at hs
    simp at hs
    exact (not_le.mpr (by rfl )) hs
  have htS := ht S.v
  field_simp at htS
  exact (htS h).elim



lemma parametersFLT_val (S : parametersFLT) : S.v = 0 ∨ S.w = 0 := by
  have hx := (FLTThree S.v S.w (-1))
  have hS := S.hcube
  simp at hx
  by_contra hwv
  rw [not_or] at hwv
  have hxt := hx.mt
  simp at hxt
  have hm1 : (-1)^3 = (-1 : ℚ) := by rfl
  rw [← hm1] at hS
  have hxtt := hxt hwv.right hS
  exact (hwv.left hxtt)


@[ext]
lemma parametersFLT.ext {S T : parametersFLT}
  (hQ : S.Q = T.Q) (hv : S.v = T.v) (hw : S.w = T.w)  : S = T := by
  cases' S
  simp_all only

@[simps!]
def parametersFLTToParameters (S : parametersFLT) : parameters :=
  ⟨S.Q,   3 * S.Q * (S.v - S.w) / (S.v + S.w),  - 6 * S.Q  / (S.v + S.w)⟩

-- ((S.v+S.w)^3 + 3 * (S.v - S.w)^2 * (S.v+S.w) + 4)/ (S.v+S.w)^3
lemma cube_for_parametersFLT (S : parametersFLT) :
    accCubicParameters (parametersFLTToParameters S) =
     - 216 * S.Q ^ 3 * (S.v ^ 3 + S.w ^ 3 + 1) / (S.v + S.w) ^ 3 := by
  have h1 : accCubicParameters (parametersFLTToParameters S) =
      - 54 * S.Q^3 * ( 1 + 3 * (S.v - S.w)^2 / (S.v+S.w)^2 + 4 / (S.v+S.w)^3) := by
    field_simp
    ring
  have hy := S.hvw
  have h2 : ( 1 + 3 * (S.v - S.w)^2 / (S.v+S.w)^2 + 4 / (S.v+S.w)^3) =
      ((S.v+S.w)^3 + 3 * (S.v - S.w)^2 * (S.v+S.w) + 4)/ (S.v+S.w)^3 := by
    field_simp
    ring
  rw [h2] at h1
  have h3 : ((S.v+S.w)^3 + 3 * (S.v - S.w)^2 * (S.v+S.w) + 4) = 4 * (S.v^3 + S.w^3 + 1) := by
    ring
  rw [h3] at h1
  rw [h1]
  ring

def parameterFLTEquiv : parametersFLT ≃ parametersCubicQNEZero where
  toFun S :=
    ⟨⟨parametersFLTToParameters S, by
      rw [cube_for_parametersFLT]
      rw [S.hcube]
      ring
      ⟩, by simp; exact S.hQ ⟩
  invFun S := ⟨S.val.val.Q, - (3 * S.val.val.Q + S.val.val.Y) / S.val.val.E,
     - ( 3 * S.val.val.Q - S.val.val.Y)/ S.val.val.E,
    by exact S.Q, by
      field_simp
      have hQ := S.Q
      rw [not_or]
      apply And.intro
      ring_nf
      field_simp
      by_contra h
      exact hQ ((accCubicParameters_E_zero S.val.val h).mp S.val.cube)
     , by
      have hQ := S.Q
      have hE : S.val.val.E ≠ 0 := by
        by_contra h
        exact hQ ((accCubicParameters_E_zero S.val.val h).mp S.val.cube)
      field_simp [hQ, hE]
      have hS := S.val.cube
      simp at hS
      linear_combination hS
      ⟩
  left_inv S := by
    have hvw := S.hvw
    have hQ := S.hQ
    apply parametersFLT.ext
    simp
    field_simp
    ring
    field_simp
    ring
  right_inv S := by
    have hQ := S.Q
    have hE : S.val.val.E ≠ 0 := by
      by_contra h
      exact hQ ((accCubicParameters_E_zero S.val.val h).mp S.val.cube)
    apply parametersCubicQNEZero.ext
    apply parameters.ext
    simp
    field_simp
    ring_nf
    field_simp [hQ, hE]
    ring
    field_simp
    ring_nf
    field_simp [hQ, hE]
    ring



theorem AnomalyFreeNotGrav_then_grav (S : AnomalyFreeNotGrav) :
    accGrav S.val.val = 0 := by
  by_cases hQ : S.val.val.Q = 0
  simp [accGrav]
  rw [hQ]
  have hSU2 := S.val.SU2
  have hSU3 := S.val.SU3
  simp_all
  let P := parametersCubicEquiv.invFun S
  rw [show S.val.val.E =0 from (accCubicParameters_Q_zero P.val hQ).mp P.cube]
  linear_combination 3 * hSU3
  let S' : parametersCubicQNEZero := ⟨parametersCubicEquiv.invFun S, hQ⟩
  have hS :  S = parametersCubicEquiv.toFun (parameterFLTEquiv.toFun (
    parameterFLTEquiv.invFun (S') )).val := by
    simp
  let S'' :=  parameterFLTEquiv.invFun (S')
  have hS'' : S'' =  parameterFLTEquiv.invFun (S')  := rfl
  rw [hS, ← hS'']
  simp [parameterFLTEquiv, parametersCubicEquiv, parameterization]
  rcases parametersFLT_val S'' with hv | hw
  have hw := parametersFLT_v_zero S'' hv
  rw [hv, hw]
  ring
  have hv := parametersFLT_w_zero S'' hw
  rw [hv, hw]
  ring

def AnomalyFreeNotGravEquivAnomalyFree : AnomalyFreeNotGrav ≃ AnomalyFree where
  toFun S := ⟨⟨S.val.val, AnomalyFreeNotGrav_then_grav S, S.val.SU2, S.val.SU3⟩, S.cube⟩
  invFun S := ⟨⟨S.val.val, S.val.SU2, S.val.SU3⟩, S.cube⟩
  left_inv S := by
    apply AnomalyFreeNotGrav.ext
    rfl
  right_inv S := by
    apply AnomalyFree.ext
    rfl

end LohitsiriTong

end SMOneFamily
