/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Module.Equiv
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.BigOperators.Fin
import AnomalyCancellationInLean.Basic

universe v u
open Nat


open  Finset

namespace PureU1
open BigOperators

@[simps!]
def PureU1Charges (n : ℕ) : ACCSystemCharges := ACCSystemChargesMk n

open BigOperators in
def accGrav (n : ℕ) : ((PureU1Charges n).charges →ₗ[ℚ] ℚ) where
  toFun S := ∑ i : Fin n, S i
  map_add' S T := Finset.sum_add_distrib
  map_smul' a S := by
   simp [HSMul.hSMul, SMul.smul]
   rw [← Finset.mul_sum]
   rfl

@[simps!]
def accCubeTriLinSymm {n : ℕ} : TriLinearSymm (PureU1Charges n).charges where
  toFun S := ∑ i, S.1 i * S.2.1 i * S.2.2 i
  map_smul₁' a S L T := by
    simp [HSMul.hSMul]
    rw [Finset.mul_sum]
    apply Fintype.sum_congr
    intro i
    ring
  map_add₁' S L T R := by
    simp
    rw [← Finset.sum_add_distrib]
    apply Fintype.sum_congr
    intro i
    ring
  swap₁' S L T := by
    simp
    apply Fintype.sum_congr
    intro i
    ring
  swap₂' S L T := by
    simp
    apply Fintype.sum_congr
    intro i
    ring

lemma accCubeTriLinSymm_cast {n m : ℕ} (h : m = n)
    (S :  (PureU1Charges n).charges × (PureU1Charges n).charges × (PureU1Charges n).charges) :
    accCubeTriLinSymm S = ∑ i : Fin m,
      S.1 (Fin.cast h i) * S.2.1 (Fin.cast h i) * S.2.2 (Fin.cast h i) := by
  rw [← accCubeTriLinSymm.toFun_eq_coe, accCubeTriLinSymm]
  simp
  rw [Finset.sum_equiv (Fin.castIso h).symm.toEquiv]
  intro i
  simp
  intro i
  simp

@[simp]
def accCube (n : ℕ)  : HomogeneousCubic ((PureU1Charges n).charges) :=
  (accCubeTriLinSymm).toCubic


lemma accCube_explicit (n : ℕ) (S : (PureU1Charges n).charges) :
    accCube n S = ∑ i : Fin n, S i ^ 3:= by
  rw [accCube, TriLinearSymm.toCubic]
  change  accCubeTriLinSymm.toFun (S, S, S) = _
  rw [accCubeTriLinSymm]
  simp
  apply Finset.sum_congr
  simp
  ring_nf
  simp



end PureU1

@[simps!]
def PureU1 (n : ℕ): ACCSystem where
  numberLinear := 1
  linearACCs := fun i =>
    match i with
    | 0 => PureU1.accGrav n
  numberQuadratic := 0
  quadraticACCs := Fin.elim0
  cubicACC := PureU1.accCube n

def pureU1_eq_charges {n m : ℕ} (h : n = m):
    (PureU1 n).charges  ≃ₗ[ℚ] (PureU1 m).charges where
  toFun f := f ∘ Fin.cast h.symm
  invFun f := f ∘ Fin.cast h
  map_add' _ _ := rfl
  map_smul' _ _:= rfl
  left_inv _ := rfl
  right_inv _ := rfl

open BigOperators

lemma pureU1_linear {n : ℕ} (S : (PureU1 n.succ).LinSols) :
    ∑ i, S.val i = 0 := by
  have hS := S.linearSol
  simp at hS
  exact hS 0

lemma pureU1_cube {n : ℕ} (S : (PureU1 n.succ).Sols) :
    ∑ i, (S.val i) ^ 3 = 0 := by
  have hS := S.cubicSol
  erw [PureU1.accCube_explicit] at hS
  exact hS

lemma pureU1_last {n : ℕ} (S : (PureU1 n.succ).LinSols) :
    S.val (Fin.last n) = - ∑ i : Fin n, S.val i.castSucc := by
  have hS := pureU1_linear S
  simp at hS
  rw [Fin.sum_univ_castSucc] at hS
  linear_combination hS

lemma pureU1_anomalyFree_ext {n : ℕ} {S T : (PureU1 n.succ).LinSols}
    (h : ∀ (i : Fin n), S.val i.castSucc = T.val i.castSucc) : S = T := by
  apply ACCSystemLinear.LinSols.ext
  funext i
  by_cases hi : i ≠ Fin.last n
  have hiCast : ∃ j : Fin n, j.castSucc = i := by
    exact Fin.exists_castSucc_eq.mpr hi
  obtain ⟨j, hj⟩ := hiCast
  rw [← hj]
  exact h j
  simp at hi
  rw [hi]
  rw [pureU1_last, pureU1_last]
  simp
  apply Finset.sum_congr
  simp
  intro j _
  exact h j

namespace PureU1

lemma sum_of_charges {n : ℕ} (f : Fin k → (PureU1 n).charges) (j : Fin n) :
    (∑ i : Fin k, (f i)) j = ∑ i : Fin k, (f i) j := by
  induction k
  simp
  rfl
  rename_i k hl
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hlt := hl (f ∘ Fin.castSucc)
  erw [← hlt]
  simp


lemma sum_of_anomaly_free_linear {n : ℕ} (f : Fin k → (PureU1 n).LinSols) (j : Fin n) :
    (∑ i : Fin k, (f i)).1 j = (∑ i : Fin k, (f i).1 j) := by
  induction k
  simp
  rfl
  rename_i k hl
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hlt := hl (f ∘ Fin.castSucc)
  erw [← hlt]
  simp


end PureU1
