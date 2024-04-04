/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.PureU1.Basic
import Mathlib.Tactic.Polyrith
import Mathlib.RepresentationTheory.Basic
-- https://arxiv.org/pdf/1912.04804.pdf

namespace PureU1

open BigOperators

variable {n : ℕ}
namespace BasisLinear

@[simp]
def asCharges (j : Fin n) : (PureU1 n.succ).charges :=
 (fun i =>
  if i = j.castSucc then
    1
  else
    if i = Fin.last n then
      - 1
    else
      0)

lemma asCharges_eq_castSucc (j : Fin n) :
    asCharges j (Fin.castSucc j) = 1 := by
  simp [asCharges]

lemma asCharges_ne_castSucc {k j : Fin n} (h : k ≠ j) :
    asCharges k (Fin.castSucc j) = 0 := by
  simp [asCharges]
  split
  rename_i h1
  rw [Fin.ext_iff] at h1
  simp_all
  rw [Fin.ext_iff] at h
  simp_all
  split
  rename_i h1 h2
  rw [Fin.ext_iff] at h1 h2
  simp at h1 h2
  have hj : j.val < n := by
    exact j.prop
  simp_all
  rfl

@[simps!]
def asAnomalyFreeLinear (j : Fin n) : (PureU1 n.succ).AnomalyFreeLinear :=
  ⟨asCharges j, by
    intro i
    simp at i
    match i with
    | 0 =>
    simp only [ Fin.isValue, PureU1_linearACCs, accGrav,
      LinearMap.coe_mk, AddHom.coe_mk, Fin.coe_eq_castSucc]
    rw [Fin.sum_univ_castSucc]
    rw [Finset.sum_eq_single j]
    simp
    have hn : ¬ (Fin.last n = Fin.castSucc j) := by
      have hj := j.prop
      rw [Fin.ext_iff]
      simp
      omega
    split
    rename_i ht
    exact (hn ht).elim
    rfl
    intro k _ hkj
    exact asCharges_ne_castSucc hkj.symm
    intro hk
    simp at hk⟩


lemma sum_of_vectors {n : ℕ} (f : Fin k → (PureU1 n).AnomalyFreeLinear) (j : Fin n) :
    (∑ i : Fin k, (f i)).1 j = (∑ i : Fin k, (f i).1 j) := by
  induction k
  simp
  rfl
  rename_i k l hl
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hlt := hl (f ∘ Fin.castSucc)
  erw [← hlt]
  simp


noncomputable
def coordinateMap : ((PureU1 n.succ).AnomalyFreeLinear) ≃ₗ[ℚ] Fin n →₀ ℚ where
  toFun S := Finsupp.equivFunOnFinite.invFun (S.1 ∘ Fin.castSucc)
  map_add' S T := by
    simp
    ext
    simp
  map_smul' a S := by
    simp
    ext
    simp
    rfl
  invFun f := ∑ i : Fin n, f i • asAnomalyFreeLinear i
  left_inv S := by
    simp
    apply pureU1_anomalyFree_ext
    intro j
    rw [sum_of_vectors]
    simp only [HSMul.hSMul, SMul.smul,  PureU1_numberCharges,
      asAnomalyFreeLinear_val, Equiv.toFun_as_coe,
      Fin.coe_eq_castSucc, mul_ite, mul_one, mul_neg, mul_zero, Equiv.invFun_as_coe]
    rw [Finset.sum_eq_single j]
    simp
    intro k _ hkj
    rw [asCharges_ne_castSucc hkj]
    simp
    simp
  right_inv f := by
    simp
    ext
    rename_i j
    simp
    rw [sum_of_vectors]
    simp only [HSMul.hSMul, SMul.smul, PureU1_numberCharges,
      asAnomalyFreeLinear_val, Equiv.toFun_as_coe,
      Fin.coe_eq_castSucc, mul_ite, mul_one, mul_neg, mul_zero, Equiv.invFun_as_coe]
    rw [Finset.sum_eq_single j]
    simp
    intro k _ hkj
    rw [asCharges_ne_castSucc hkj]
    simp
    simp

noncomputable
def asBasis : Basis (Fin n) ℚ ((PureU1 n.succ).AnomalyFreeLinear) where
  repr := coordinateMap

instance : Module.Finite ℚ ((PureU1 n.succ).AnomalyFreeLinear) :=
   Module.Finite.of_basis asBasis

lemma finrank_AnomalyFreeLinear :
    FiniteDimensional.finrank ℚ (((PureU1 n.succ).AnomalyFreeLinear)) = n := by
  have h  :=  Module.mk_finrank_eq_card_basis (@asBasis n)
  simp_all
  simp [FiniteDimensional.finrank]
  rw [h]
  simp_all only [Cardinal.toNat_natCast]


end BasisLinear


end PureU1
