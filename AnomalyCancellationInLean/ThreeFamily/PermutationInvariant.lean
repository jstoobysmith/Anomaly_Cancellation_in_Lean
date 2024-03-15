/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.Basics
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.RepresentationTheory.Basic


@[simps!]
def threeFamilyChargeMap (fQ fU fD fL fE fN : Fin 3 → Fin 3) :
    threeFamilyCharge →ₗ[ℚ] threeFamilyCharge where
  toFun := fun S => threeFamilyChargeMk
    (S.Q ∘ fQ) (S.U ∘ fU) (S.D ∘ fD) (S.L ∘ fL) (S.E ∘ fE) (S.N ∘ fN)
  map_add' := by
    intro S T
    apply threeFamilyCharge.ext <;>
      simp <;> split <;> rfl
  map_smul' := by
    intro a S
    apply threeFamilyCharge.ext <;>
      simp [threeFamilyChargeMk] <;> split <;> rfl


@[simp]
def permGroup := (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)
    × Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))

instance : Group permGroup :=
  @Prod.instGroup _ _ _ _

@[simps!]
def rep : Representation ℚ permGroup threeFamilyCharge where
  toFun := fun f =>
    threeFamilyChargeMap f.1.2 f.2.1.2 f.2.2.1.2 f.2.2.2.1.2 f.2.2.2.2.1.2 f.2.2.2.2.2.2
  map_mul' :=by
    intro f g
    simp
    apply LinearMap.ext
    intro S
    simp
    simp [threeFamilyChargeMap]
    rw [threeFamilyChargeMk_Q, threeFamilyChargeMk_U, threeFamilyChargeMk_D,
    threeFamilyChargeMk_L, threeFamilyChargeMk_E, threeFamilyChargeMk_N]
    repeat rw [Function.comp.assoc]
    rfl
  map_one' := by
    simp [threeFamilyChargeMap]
    rfl

lemma f_cond (f : Equiv.Perm (Fin 3)) :
    (f 0 = 0 ∧ f 1 = 1 ∧ f 2 = 2)
    ∨ (f 0 = 2 ∧ f 1 = 0 ∧ f 2 = 1)
    ∨ (f 0 = 1 ∧ f 1 = 2 ∧ f 2 = 0)
    ∨ (f 0 = 0 ∧ f 1 = 2 ∧ f 2 = 1)
    ∨ (f 0 = 1 ∧ f 1 = 0 ∧ f 2 = 2)
    ∨ (f 0 = 2 ∧ f 1 = 1 ∧ f 2 = 0) := by
  let a0 := f 0
  let a1 := f 1
  let a2 := f 2
  have h0 : a0 = f 0 := rfl
  have h1 : a1 = f 1 := rfl
  have h2 : a2 = f 2 := rfl
  rw [← h0, ← h1, ← h2]
  have h01 : ¬ (a0 = a1) := (Equiv.apply_eq_iff_eq f).mp.mt (by simp)
  have h02 : ¬ (a0 = a2) := (Equiv.apply_eq_iff_eq f).mp.mt (by simp)
  have h12 : ¬ (a1 = a2) := (Equiv.apply_eq_iff_eq f).mp.mt (by simp)
  match a0, a1, a2 with
  | 0, 1, 2 => simp
  | 2, 0, 1 => simp
  | 1, 2, 0 => simp
  | 0, 2, 1 => simp
  | 1, 0, 2 => simp
  | 2, 1, 0 => simp
  | 0, 0, 0 => exact (h01 rfl).elim
  | 0, 0, 1 => exact (h01 rfl).elim
  | 0, 0, 2 => exact (h01 rfl).elim
  | 1, 1, 0 => exact (h01 rfl).elim
  | 1, 1, 1 => exact (h01 rfl).elim
  | 1, 1, 2 => exact (h01 rfl).elim
  | 2, 2, 0 => exact (h01 rfl).elim
  | 2, 2, 1 => exact (h01 rfl).elim
  | 2, 2, 2 => exact (h01 rfl).elim
  | 0, 1, 0 => exact (h02 rfl).elim
  | 0, 2, 0 => exact (h02 rfl).elim
  | 1, 0, 1 => exact (h02 rfl).elim
  | 1, 2, 1 => exact (h02 rfl).elim
  | 2, 0, 2 => exact (h02 rfl).elim
  | 2, 1, 2 => exact (h02 rfl).elim
  | 1, 0, 0 => exact (h12 rfl).elim
  | 2, 0, 0 => exact (h12 rfl).elim
  | 0, 1, 1 => exact (h12 rfl).elim
  | 2, 1, 1 => exact (h12 rfl).elim
  | 0, 2, 2 => exact (h12 rfl).elim
  | 1, 2, 2 => exact (h12 rfl).elim

lemma sum_invariant (g : Fin 3 → ℚ) (f : Equiv.Perm (Fin 3)) :
    g 0 + g 1 + g 2 = (g ∘ f) 0 + (g ∘ f) 1 + (g ∘ f) 2 := by
  simp only [Fin.isValue, Function.comp_apply]
  rcases f_cond f with h | h | h | h | h | h
  all_goals rw [h.1, h.2.1, h.2.2]
  all_goals ring

lemma QSum_invariant (S : threeFamilyCharge) (f : permGroup) :
    (rep f S).QSum = S.QSum := (sum_invariant S.Q f.1.symm).symm

lemma USum_invariant (S : threeFamilyCharge) (f : permGroup) :
    (rep f S).USum = S.USum := (sum_invariant S.U f.2.1.symm).symm

lemma DSum_invariant (S : threeFamilyCharge) (f : permGroup) :
    (rep f S).DSum = S.DSum := (sum_invariant S.D f.2.2.1.symm).symm

lemma LSum_invariant (S : threeFamilyCharge) (f : permGroup) :
    (rep f S).LSum = S.LSum := (sum_invariant S.L f.2.2.2.1.symm).symm

lemma ESum_invariant (S : threeFamilyCharge) (f : permGroup) :
    (rep f S).ESum = S.ESum := (sum_invariant S.E f.2.2.2.2.1.symm).symm

lemma NSum_invariant (S : threeFamilyCharge) (f : permGroup) :
    (rep f S).NSum = S.NSum := (sum_invariant S.N f.2.2.2.2.2.symm).symm

def anomalyFreeLinearMap (f : permGroup) :
    AnomalyFreeLinear →ₗ[ℚ] AnomalyFreeLinear where
  toFun S := ⟨
      rep f S.val,
      by
        simp only [accGrav]
        rw [QSum_invariant, USum_invariant, DSum_invariant, LSum_invariant, ESum_invariant,
        NSum_invariant]
        exact S.Grav,
      by
        simp only [accSU2]
        rw [QSum_invariant, LSum_invariant]
        exact S.SU2,
      by
        simp only [accSU3]
        rw [QSum_invariant, USum_invariant, DSum_invariant]
        exact S.SU3,
      by
        simp only [accYY]
        rw [QSum_invariant, USum_invariant, DSum_invariant, LSum_invariant, ESum_invariant]
        exact S.YY ⟩
  map_add' S T := by
    apply AnomalyFreeLinear.ext
    exact (rep f).map_add' _ _
  map_smul' a S := by
    apply AnomalyFreeLinear.ext
    exact (rep f).map_smul' _ _

@[simps!]
def repAnomalyFreeLinear : Representation ℚ permGroup AnomalyFreeLinear where
  toFun := anomalyFreeLinearMap
  map_mul' f1 f2 := by
    apply LinearMap.ext
    intro S
    apply AnomalyFreeLinear.ext
    change (rep.toFun (f1 * f2)) S.val = _
    rw [rep.map_mul']
    rfl
  map_one' := by
    apply LinearMap.ext
    intro S
    apply AnomalyFreeLinear.ext
    change (rep.toFun 1) S.val = _
    rw [rep.map_one']
    rfl

instance actionAnomalyFreeQuad : MulAction permGroup AnomalyFreeQuad where
  smul f S := ⟨repAnomalyFreeLinear f S.val, by sorry⟩
  mul_smul f1 f2 S := by
    apply AnomalyFreeQuad.ext
    change (rep.toFun (f1 * f2)) S.val.val = _
    rw [rep.map_mul']
    rfl
  one_smul S := by
    apply AnomalyFreeQuad.ext
    change (rep.toFun 1) S.val.val = _
    rw [rep.map_one']
    rfl
