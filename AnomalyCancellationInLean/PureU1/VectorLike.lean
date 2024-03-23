/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.PureU1.Sort
import AnomalyCancellationInLean.PureU1.BasisLinear
universe v u

open Nat
open  Finset
open BigOperators

namespace PureU1

variable {n : ℕ}

lemma split_equal (n : ℕ) : n + n = 2 * n := (Nat.two_mul n).symm


lemma split_odd (n : ℕ) : n + 1 + n = 2 * n + 1 := by omega

@[simp]
def vectorLikeEven {n : ℕ}  (S : (PureU1 (2 * n)).charges) : Prop :=
  ∀ (i : Fin n), (sort S) (Fin.cast (split_equal n)  (Fin.castAdd n i))
  = - (sort S) (Fin.cast (split_equal n)  (Fin.natAdd n i))

namespace VectorLikeEvenPlane
lemma n_cond₂ (n : ℕ) : 1 + ((n + n) + 1) = 2 * n.succ := by
  linarith

def δ₁ (j : Fin n.succ) : Fin (2 * n.succ) :=
  Fin.cast (split_equal n.succ) (Fin.castAdd n.succ j)

def δ₂ (j : Fin n.succ) : Fin (2 * n.succ) :=
  Fin.cast (split_equal n.succ) (Fin.natAdd n.succ j)

def δ!₁ (j : Fin n) : Fin (2 * n.succ) :=
  Fin.cast (n_cond₂ n)  (Fin.natAdd 1 (Fin.castAdd 1 (Fin.castAdd n j)))

def δ!₂ (j : Fin n) : Fin (2 * n.succ) := Fin.cast (n_cond₂ n)
   (Fin.natAdd 1 (Fin.castAdd 1 (Fin.natAdd n j)))

def δ!₃ : Fin (2 * n.succ) := (Fin.cast (n_cond₂ n) (Fin.castAdd ((n + n) + 1) 0))

def δ!₄ : Fin (2 * n.succ) := (Fin.cast (n_cond₂ n) (Fin.natAdd 1 (Fin.natAdd (n + n) 0)))

lemma sum_δ₁_δ₂  (S : Fin (2 * n.succ) → ℚ) :
    ∑ i, S i = ∑ i : Fin n.succ, ((S ∘ δ₁) i + (S ∘ δ₂) i) := by
  have h1 : ∑ i, S i = ∑ i : Fin (n.succ + n.succ), S (Fin.cast (split_equal n.succ) i) := by
    rw [Finset.sum_equiv (Fin.castIso (split_equal n.succ)).symm.toEquiv]
    intro i
    simp
    intro i
    simp
  rw [h1]
  rw [Fin.sum_univ_add, Finset.sum_add_distrib]
  rfl

lemma sum_δ!₁_δ!₂  (S : Fin (2 * n.succ) → ℚ) :
    ∑ i, S i = S δ!₃ + S δ!₄ + ∑ i : Fin n,  ((S ∘ δ!₁) i + (S ∘ δ!₂) i) := by
  have h1 : ∑ i, S i = ∑ i : Fin (1 + ((n + n) + 1)), S (Fin.cast (n_cond₂ n) i) := by
    rw [Finset.sum_equiv (Fin.castIso (n_cond₂ n)).symm.toEquiv]
    intro i
    simp
    intro i
    simp
  rw [h1]
  rw [Fin.sum_univ_add, Fin.sum_univ_add, Fin.sum_univ_add, Finset.sum_add_distrib]
  simp
  repeat rw [Rat.add_assoc]
  apply congrArg
  rw [Rat.add_comm]
  rw [← Rat.add_assoc]
  nth_rewrite 2 [Rat.add_comm]
  repeat rw [Rat.add_assoc]
  nth_rewrite 2 [Rat.add_comm]
  rfl

lemma δ!₃_δ₁0 : @δ!₃ n = δ₁ 0 := by
  rfl

lemma δ!₄_δ₂Last: @δ!₄ n = δ₂ (Fin.last n) := by
  rw [Fin.ext_iff]
  simp [δ!₄, δ₂]
  omega

lemma δ!₁_δ₁ (j : Fin n) : δ!₁ j = δ₁ j.succ := by
  rw [Fin.ext_iff, δ₁, δ!₁]
  simp
  ring

lemma δ!₂_δ₂ (j : Fin n) : δ!₂ j = δ₂ j.castSucc := by
  rw [Fin.ext_iff, δ₂, δ!₂]
  simp
  ring_nf
  rw [Nat.succ_eq_add_one]
  ring

def basisAsCharges (j : Fin n.succ) : (PureU1 (2 * n.succ)).charges :=
  fun i =>
  if i = δ₁ j then
    1
  else
    if i = δ₂ j then
      - 1
    else
      0

def basis!AsCharges (j : Fin n) : (PureU1 (2 * n.succ)).charges :=
  fun i =>
  if i = δ!₁ j then
    1
  else
    if i = δ!₂ j then
      - 1
    else
      0

lemma basis_on_δ₁_self (j : Fin n.succ) : basisAsCharges j (δ₁ j) = 1 := by
  simp [basisAsCharges]

lemma basis!_on_δ!₁_self (j : Fin n) : basis!AsCharges j (δ!₁ j) = 1 := by
  simp [basis!AsCharges]

lemma basis_on_δ₁_other {k j : Fin n.succ} (h : k ≠ j) :
    basisAsCharges k (δ₁ j) = 0 := by
  simp [basisAsCharges]
  simp [δ₁, δ₂]
  split
  rename_i h1
  rw [Fin.ext_iff] at h1
  simp_all
  rw [Fin.ext_iff] at h
  simp_all
  split
  rename_i h1 h2
  simp_all
  rw [Fin.ext_iff] at h2
  simp at h2
  omega
  rfl

lemma basis!_on_δ!₁_other {k j : Fin n} (h : k ≠ j) :
    basis!AsCharges k (δ!₁ j) = 0 := by
  simp [basis!AsCharges]
  simp [δ!₁, δ!₂]
  split
  rename_i h1
  rw [Fin.ext_iff] at h1
  simp_all
  rw [Fin.ext_iff] at h
  simp_all
  split
  rename_i h1 h2
  simp_all
  rw [Fin.ext_iff] at h2
  simp at h2
  omega
  rfl

lemma basis_δ₂_eq_minus_δ₁ (j i : Fin n.succ) :
    basisAsCharges j (δ₂ i) = - basisAsCharges j (δ₁ i) := by
  simp [basisAsCharges, δ₂, δ₁]
  split <;> split
  any_goals split
  any_goals split
  any_goals rfl
  all_goals rename_i h1 h2
  all_goals rw [Fin.ext_iff] at h1 h2
  all_goals simp_all
  all_goals rename_i h3
  all_goals rw [Fin.ext_iff] at h3
  all_goals simp_all
  all_goals omega

lemma basis!_δ!₂_eq_minus_δ!₁ (j i : Fin n) :
    basis!AsCharges j (δ!₂ i) = - basis!AsCharges j (δ!₁ i) := by
  simp [basis!AsCharges, δ!₂, δ!₁]
  split <;> split
  any_goals split
  any_goals split
  any_goals rfl
  all_goals rename_i h1 h2
  all_goals rw [Fin.ext_iff] at h1 h2
  all_goals simp_all
  subst h1
  exact Fin.elim0 i
  all_goals rename_i h3
  all_goals rw [Fin.ext_iff] at h3
  all_goals simp_all
  all_goals omega

lemma basis_on_δ₂_self (j : Fin n.succ) : basisAsCharges j (δ₂ j) = - 1 := by
  rw [basis_δ₂_eq_minus_δ₁, basis_on_δ₁_self]

lemma basis!_on_δ!₂_self (j : Fin n) : basis!AsCharges j (δ!₂ j) = - 1 := by
  rw [basis!_δ!₂_eq_minus_δ!₁, basis!_on_δ!₁_self]

lemma basis_on_δ₂_other {k j : Fin n.succ} (h : k ≠ j) : basisAsCharges k (δ₂ j) = 0 := by
  rw [basis_δ₂_eq_minus_δ₁, basis_on_δ₁_other h]
  rfl

lemma basis!_on_δ!₂_other {k j : Fin n} (h : k ≠ j) : basis!AsCharges k (δ!₂ j) = 0 := by
  rw [basis!_δ!₂_eq_minus_δ!₁, basis!_on_δ!₁_other h]
  rfl

lemma basis!_on_δ!₃ (j : Fin n) : basis!AsCharges j δ!₃ = 0 := by
  simp [basis!AsCharges]
  split <;> rename_i h
  rw [Fin.ext_iff] at h
  simp [δ!₃, δ!₁] at h
  omega
  split <;> rename_i h2
  rw [Fin.ext_iff] at h2
  simp [δ!₃, δ!₂] at h2
  omega
  rfl

lemma basis!_on_δ!₄ (j : Fin n) : basis!AsCharges j δ!₄ = 0 := by
  simp [basis!AsCharges]
  split <;> rename_i h
  rw [Fin.ext_iff] at h
  simp [δ!₄, δ!₁] at h
  omega
  split <;> rename_i h2
  rw [Fin.ext_iff] at h2
  simp [δ!₄, δ!₂] at h2
  omega
  rfl

lemma basis_linearACC (j : Fin n.succ) : (accGrav (2 * n.succ)) (basisAsCharges j) = 0 := by
  rw [accGrav]
  simp
  rw [sum_δ₁_δ₂]
  simp [basis_δ₂_eq_minus_δ₁]

lemma basis!_linearACC (j : Fin n) : (accGrav (2 * n.succ)) (basis!AsCharges j) = 0 := by
  rw [accGrav]
  simp
  rw [sum_δ!₁_δ!₂, basis!_on_δ!₃, basis!_on_δ!₄]
  simp [basis!_δ!₂_eq_minus_δ!₁]

lemma basis_accCube (j : Fin n.succ) :
    (PureU1 (2 * n.succ)).cubicACC.toFun (basisAsCharges j) = 0 := by
  simp
  rw [sum_δ₁_δ₂]
  apply Finset.sum_eq_zero
  intro i _
  simp [basis_δ₂_eq_minus_δ₁]
  ring

lemma basis!_accCube (j : Fin n) :
    (PureU1 (2 * n.succ)).cubicACC.toFun (basis!AsCharges j) = 0 := by
  simp
  rw [sum_δ!₁_δ!₂]
  rw [basis!_on_δ!₄, basis!_on_δ!₃]
  simp
  apply Finset.sum_eq_zero
  intro i _
  simp [basis!_δ!₂_eq_minus_δ!₁]
  ring


@[simps!]
def basis (j : Fin n.succ) : (PureU1 (2 * n.succ)).AnomalyFreeLinear :=
  ⟨basisAsCharges j, by
    intro i
    simp at i
    match i with
    | 0 =>
    exact basis_linearACC j⟩

@[simps!]
def basis! (j : Fin n) : (PureU1 (2 * n.succ)).AnomalyFreeLinear :=
  ⟨basis!AsCharges j, by
    intro i
    simp at i
    match i with
    | 0 =>
    exact basis!_linearACC j⟩

def basisa : (Fin n.succ) ⊕ (Fin n) → (PureU1 (2 * n.succ)).AnomalyFreeLinear := fun i =>
  match i with
  | .inl i => basis i
  | .inr i => basis! i

def P (f : Fin n.succ → ℚ) : (PureU1 (2 * n.succ)).charges := ∑ i, f i • basisAsCharges i

def P! (f : Fin n → ℚ) : (PureU1 (2 * n.succ)).charges := ∑ i, f i • basis!AsCharges i

def Pa (f : Fin n.succ → ℚ) (g : Fin n → ℚ) : (PureU1 (2 * n.succ)).charges := P f + P! g

lemma P_δ₁ (f : Fin n.succ → ℚ) (j : Fin n.succ) : P f (δ₁ j) = f j := by
  rw [P, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  rw [basis_on_δ₁_self]
  simp
  intro k _ hkj
  rw [basis_on_δ₁_other hkj]
  simp only [mul_zero]
  simp only [mem_univ, not_true_eq_false, _root_.mul_eq_zero, IsEmpty.forall_iff]

lemma P!_δ!₁ (f : Fin n → ℚ)  (j : Fin n) : P! f (δ!₁ j) = f j := by
  rw [P!, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  rw [basis!_on_δ!₁_self]
  simp
  intro k _ hkj
  rw [basis!_on_δ!₁_other hkj]
  simp only [mul_zero]
  simp only [mem_univ, not_true_eq_false, _root_.mul_eq_zero, IsEmpty.forall_iff]

lemma Pa_δ!₁ (f : Fin n.succ → ℚ) (g : Fin n → ℚ) (j : Fin n) : Pa f g (δ!₁ j) = f j.succ + g j := by
  rw [Pa]
  simp
  rw [P!_δ!₁, δ!₁_δ₁, P_δ₁]

lemma P_δ₂ (f : Fin n.succ → ℚ) (j : Fin n.succ) : P f (δ₂ j) = - f j := by
  rw [P, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  rw [basis_on_δ₂_self]
  simp
  intro k _ hkj
  rw [basis_on_δ₂_other hkj]
  simp
  simp

lemma P!_δ!₂ (f : Fin n → ℚ) (j : Fin n) : P! f (δ!₂ j) = - f j := by
  rw [P!, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  rw [basis!_on_δ!₂_self]
  simp
  intro k _ hkj
  rw [basis!_on_δ!₂_other hkj]
  simp
  simp

lemma Pa_δ!₂ (f : Fin n.succ → ℚ) (g : Fin n → ℚ) (j : Fin n) :
    Pa f g (δ!₂ j) = - f j.castSucc - g j := by
  rw [Pa]
  simp
  rw [P!_δ!₂, δ!₂_δ₂, P_δ₂]
  ring

lemma P!_δ!₃ (f : Fin n → ℚ) : P! f (δ!₃) = 0 := by
  rw [P!, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul, basis!_on_δ!₃]

lemma Pa_δ!₃  (f : Fin n.succ → ℚ) (g : Fin n → ℚ) :  Pa f g (δ!₃) =  f 0 := by
  rw [Pa]
  simp
  rw [P!_δ!₃, δ!₃_δ₁0, P_δ₁]
  simp

lemma P!_δ!₄ (f : Fin n → ℚ) : P! f (δ!₄) = 0 := by
  rw [P!, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul, basis!_on_δ!₄]

lemma Pa_δ!₄  (f : Fin n.succ → ℚ) (g : Fin n → ℚ) :  Pa f g (δ!₄) = - f (Fin.last n) := by
  rw [Pa]
  simp
  rw [P!_δ!₄, δ!₄_δ₂Last, P_δ₂]
  simp

lemma P_δ₁_δ₂ (f : Fin n.succ → ℚ)  : P f ∘ δ₂ = - P f ∘ δ₁ := by
  funext j
  simp
  rw [P_δ₁, P_δ₂]

lemma P_linearACC (f : Fin n.succ → ℚ) : (accGrav (2 * n.succ)) (P f) = 0 := by
  rw [accGrav]
  simp
  rw [sum_δ₁_δ₂]
  simp [P_δ₂, P_δ₁]

lemma P_accCube (f : Fin n.succ → ℚ) : (PureU1 (2 * n.succ)).cubicACC.toFun (P f) = 0 := by
  simp
  rw [sum_δ₁_δ₂]
  apply Finset.sum_eq_zero
  intro i _
  simp [P_δ₁, P_δ₂]
  ring

lemma P_P_P!_accCube (g : Fin n.succ → ℚ) (j : Fin n) :
    accCubeTriLinSymm.toFun (P g, P g, basis!AsCharges j)
    = g (j.succ) ^ 2 - g (j.castSucc) ^ 2 := by
  simp [accCubeTriLinSymm]
  rw [sum_δ!₁_δ!₂, basis!_on_δ!₃, basis!_on_δ!₄]
  simp
  rw [Finset.sum_eq_single j, basis!_on_δ!₁_self, basis!_on_δ!₂_self]
  simp [δ!₁_δ₁, δ!₂_δ₂]
  rw [P_δ₁, P_δ₂]
  ring
  intro k _ hkj
  erw [basis!_on_δ!₁_other hkj.symm, basis!_on_δ!₂_other hkj.symm]
  simp
  simp

lemma P_P!_P!_accCube (g : Fin n → ℚ) (j : Fin n.succ) :
    accCubeTriLinSymm.toFun (P! g, P! g, basisAsCharges j)
    =  (P! g (δ₁ j))^2 -  (P! g (δ₂ j))^2 := by
  simp [accCubeTriLinSymm]
  rw [sum_δ₁_δ₂]
  simp
  rw [Finset.sum_eq_single j, basis_on_δ₁_self, basis_on_δ₂_self]
  simp [δ!₁_δ₁, δ!₂_δ₂]
  ring
  intro k _ hkj
  erw [basis_on_δ₁_other hkj.symm, basis_on_δ₂_other hkj.symm]
  simp
  simp

lemma P_zero (f : Fin n.succ → ℚ) (h : P f = 0) : ∀ i, f i = 0 := by
  intro i
  erw [← P_δ₁ f]
  rw [h]
  rfl

lemma P!_zero (f : Fin n → ℚ) (h : P! f = 0) : ∀ i, f i = 0 := by
  intro i
  rw [← P!_δ!₁ f]
  rw [h]
  rfl

lemma Pa_zero (f : Fin n.succ → ℚ) (g : Fin n → ℚ) (h : Pa f g = 0) :
    ∀ i, f i = 0 := by
  have h₃ := Pa_δ!₃ f g
  rw [h] at h₃
  simp at h₃
  intro i
  have hinduc (iv : ℕ) (hiv : iv < n.succ) : f ⟨iv, hiv⟩ = 0 := by
    induction iv
    exact h₃.symm
    rename_i iv hi
    have hivi : iv < n.succ := by omega
    have hi2 := hi hivi
    have h1 := Pa_δ!₁ f g ⟨iv, by omega⟩
    have h2 := Pa_δ!₂ f g ⟨iv, by omega⟩
    rw [h] at h1 h2
    simp at h1 h2
    erw [hi2] at h2
    simp at h2
    rw [h2] at h1
    simp at h1
    exact h1.symm
  exact hinduc i.val i.prop

lemma Pa_zero! (f : Fin n.succ → ℚ) (g : Fin n → ℚ) (h : Pa f g = 0) :
    ∀ i, g i = 0 := by
  have hf := Pa_zero f g h
  rw [Pa, P] at h
  simp [hf] at h
  exact P!_zero g h

def P' (f : Fin n.succ → ℚ) : (PureU1 (2 * n.succ)).AnomalyFreeLinear := ∑ i, f i • basis i

def P!' (f : Fin n → ℚ) : (PureU1 (2 * n.succ)).AnomalyFreeLinear := ∑ i, f i • basis! i

def Pa' (f : (Fin n.succ) ⊕ (Fin n) → ℚ) : (PureU1 (2 * n.succ)).AnomalyFreeLinear :=
    ∑ i, f i • basisa i

lemma Pa'_P'_P!' (f : (Fin n.succ) ⊕ (Fin n) → ℚ) :
    Pa' f = P' (f ∘ Sum.inl) + P!' (f ∘ Sum.inr):= by
  exact Fintype.sum_sum_type _

lemma P'_val (f : Fin n.succ → ℚ) : (P' f).val = P f := by
  simp [P', P]
  funext i
  rw [sum_of_anomaly_free_linear, sum_of_charges]
  simp [HSMul.hSMul]

lemma P!'_val (f : Fin n → ℚ) : (P!' f).val = P! f := by
  simp [P!', P!]
  funext i
  rw [sum_of_anomaly_free_linear, sum_of_charges]
  simp [HSMul.hSMul]

theorem basis_linear_independent : LinearIndependent ℚ (@basis n) := by
  apply Fintype.linearIndependent_iff.mpr
  intro f h
  change P' f = 0 at h
  have h1 : (P' f).val = 0 := by
    simp [h]
    rfl
  rw [P'_val] at h1
  exact P_zero f h1

theorem basis!_linear_independent : LinearIndependent ℚ (@basis! n) := by
  apply Fintype.linearIndependent_iff.mpr
  intro f h
  change P!' f = 0 at h
  have h1 : (P!' f).val = 0 := by
    simp [h]
    rfl
  rw [P!'_val] at h1
  exact P!_zero f h1

theorem basisa_linear_independent : LinearIndependent ℚ (@basisa n) := by
  apply Fintype.linearIndependent_iff.mpr
  intro f h
  change Pa' f = 0 at h
  have h1 : (Pa' f).val = 0 := by
    simp [h]
    rfl
  rw [Pa'_P'_P!'] at h1
  change (P' (f ∘ Sum.inl)).val + (P!' (f ∘ Sum.inr)).val = 0 at h1
  rw [P!'_val, P'_val] at h1
  change Pa (f ∘ Sum.inl) (f ∘ Sum.inr) = 0 at h1
  have hf := Pa_zero (f ∘ Sum.inl) (f ∘ Sum.inr) h1
  have hg := Pa_zero! (f ∘ Sum.inl) (f ∘ Sum.inr) h1
  intro i
  simp_all
  cases i
  simp_all
  simp_all

lemma basisa_card :  Fintype.card ((Fin n.succ) ⊕ (Fin n)) =
    FiniteDimensional.finrank ℚ (PureU1 (2 * n.succ)).AnomalyFreeLinear := by
  erw [BasisLinear.finrank_AnomalyFreeLinear]
  simp
  omega

noncomputable def basisaAsBasis :
    Basis (Fin (succ n) ⊕ Fin n) ℚ (PureU1 (2 * succ n)).AnomalyFreeLinear :=
  basisOfLinearIndependentOfCardEqFinrank (@basisa_linear_independent n) basisa_card

end VectorLikeEvenPlane

namespace VectorLikeEvenPlaneCompletion



end VectorLikeEvenPlaneCompletion

namespace VectorLikeOddPlane

def split_odd! (n : ℕ) : (1 + n) + n = 2 * n +1 := by
  omega

def split_adda (n : ℕ) : ((1+n)+1) + n.succ = 2 * n.succ + 1 := by
  omega

def δ₁ (j : Fin n) : Fin (2 * n + 1) :=
  Fin.cast (split_odd n) (Fin.castAdd n (Fin.castAdd 1 j))

def δ₂ (j : Fin n) : Fin (2 * n + 1) :=
  Fin.cast (split_odd n) (Fin.natAdd (n+1) j)

def δ₃ : Fin (2 * n + 1) :=
  Fin.cast (split_odd n) (Fin.castAdd n (Fin.natAdd n 1))

def δ!₁ (j : Fin n) : Fin (2 * n + 1) :=
  Fin.cast (split_odd! n) (Fin.castAdd n (Fin.natAdd 1 j))

def δ!₂ (j : Fin n) : Fin (2 * n + 1) :=
  Fin.cast (split_odd! n) (Fin.natAdd (1 + n) j)

def δ!₃ : Fin (2 * n + 1) :=
  Fin.cast (split_odd! n) (Fin.castAdd n (Fin.castAdd n 1))

def δa₁ : Fin (2 * n.succ + 1) :=
  Fin.cast (split_adda n) (Fin.castAdd n.succ (Fin.castAdd 1 (Fin.castAdd n 1)))

def δa₂ (j : Fin n) : Fin (2 * n.succ + 1) :=
  Fin.cast (split_adda n) (Fin.castAdd n.succ (Fin.castAdd 1 (Fin.natAdd 1 j)))

def δa₃ : Fin (2 * n.succ + 1) :=
  Fin.cast (split_adda n) (Fin.castAdd n.succ (Fin.natAdd (1+n) 1))

def δa₄ (j : Fin n.succ) : Fin (2 * n.succ + 1) :=
  Fin.cast (split_adda n) (Fin.natAdd ((1+n)+1) j)

lemma δa₁_δ₁ : @δa₁ n = δ₁ 0 := by
  rfl

lemma δa₁_δ!₃ : @δa₁ n = δ!₃ := by
  rfl

lemma δa₂_δ₁ (j : Fin n) : δa₂ j = δ₁ j.succ := by
  rw [Fin.ext_iff]
  simp [δa₂, δ₁]
  omega

lemma δa₂_δ!₁ (j : Fin n) : δa₂ j = δ!₁ j.castSucc := by
  rw [Fin.ext_iff]
  simp [δa₂, δ!₁]

lemma δa₃_δ₃ : @δa₃ n = δ₃ := by
  rw [Fin.ext_iff]
  simp [δa₃, δ₃]
  omega

lemma δa₃_δ!₁ : δa₃ = δ!₁ (Fin.last n) := by
  rfl

lemma δa₄_δ₂ (j : Fin n.succ) : δa₄ j = δ₂ j := by
  rw [Fin.ext_iff]
  simp [δa₄, δ₂]
  omega

lemma δa₄_δ!₂ (j : Fin n.succ) : δa₄ j = δ!₂ j := by
  rw [Fin.ext_iff]
  simp [δa₄, δ!₂]
  omega

lemma δ₂_δ!₂ (j : Fin n) : δ₂ j = δ!₂ j := by
  rw [Fin.ext_iff]
  simp [δ₂, δ!₂]
  omega

lemma sum_δ  (S : Fin (2 * n + 1) → ℚ) :
    ∑ i, S i = S δ₃ + ∑ i : Fin n, ((S ∘ δ₁) i + (S ∘ δ₂) i) := by
  have h1 : ∑ i, S i = ∑ i : Fin (n + 1 + n), S (Fin.cast (split_odd n) i) := by
    rw [Finset.sum_equiv (Fin.castIso (split_odd n)).symm.toEquiv]
    intro i
    simp
    intro i
    simp
  rw [h1]
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp
  nth_rewrite 2 [add_comm]
  rw [add_assoc]
  rw [Finset.sum_add_distrib]
  rfl

lemma sum_δ!  (S : Fin (2 * n + 1) → ℚ) :
    ∑ i, S i = S δ!₃ + ∑ i : Fin n, ((S ∘ δ!₁) i + (S ∘ δ!₂) i) := by
  have h1 : ∑ i, S i = ∑ i : Fin ((1+n)+n), S (Fin.cast (split_odd! n) i) := by
    rw [Finset.sum_equiv (Fin.castIso (split_odd! n)).symm.toEquiv]
    intro i
    simp
    intro i
    simp
  rw [h1]
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp
  rw [add_assoc]
  rw [Finset.sum_add_distrib]
  rfl


def basisAsCharges (j : Fin n) : (PureU1 (2 * n + 1)).charges :=
  fun i =>
  if i = δ₁ j then
    1
  else
    if i = δ₂ j then
      - 1
    else
      0

def basis!AsCharges (j : Fin n) : (PureU1 (2 * n + 1)).charges :=
  fun i =>
  if i = δ!₁ j then
    1
  else
    if i = δ!₂ j then
      - 1
    else
      0

lemma basis_on_δ₁_self (j : Fin n) : basisAsCharges j (δ₁ j) = 1 := by
  simp [basisAsCharges]

lemma basis!_on_δ!₁_self (j : Fin n) : basis!AsCharges j (δ!₁ j) = 1 := by
  simp [basis!AsCharges]


lemma basis_on_δ₁_other {k j : Fin n} (h : k ≠ j) :
    basisAsCharges k (δ₁ j) = 0 := by
  simp [basisAsCharges]
  simp [δ₁, δ₂]
  split
  rename_i h1
  rw [Fin.ext_iff] at h1
  simp_all
  rw [Fin.ext_iff] at h
  simp_all
  split
  rename_i h1 h2
  simp_all
  rw [Fin.ext_iff] at h2
  simp at h2
  omega
  rfl

lemma basis!_on_δ!₁_other {k j : Fin n} (h : k ≠ j) :
    basis!AsCharges k (δ!₁ j) = 0 := by
  simp [basis!AsCharges]
  simp [δ!₁, δ!₂]
  split
  rename_i h1
  rw [Fin.ext_iff] at h1
  simp_all
  rw [Fin.ext_iff] at h
  simp_all
  split
  rename_i h1 h2
  simp_all
  rw [Fin.ext_iff] at h2
  simp at h2
  omega
  rfl

lemma basis_δ₂_eq_minus_δ₁ (j i : Fin n) :
    basisAsCharges j (δ₂ i) = - basisAsCharges j (δ₁ i) := by
  simp [basisAsCharges, δ₂, δ₁]
  split <;> split
  any_goals split
  any_goals split
  any_goals rfl
  all_goals rename_i h1 h2
  all_goals rw [Fin.ext_iff] at h1 h2
  all_goals simp_all
  all_goals rename_i h3
  all_goals rw [Fin.ext_iff] at h3
  all_goals simp_all
  all_goals omega

lemma basis!_δ!₂_eq_minus_δ!₁ (j i : Fin n) :
    basis!AsCharges j (δ!₂ i) = - basis!AsCharges j (δ!₁ i) := by
  simp [basis!AsCharges, δ!₂, δ!₁]
  split <;> split
  any_goals split
  any_goals split
  any_goals rfl
  all_goals rename_i h1 h2
  all_goals rw [Fin.ext_iff] at h1 h2
  all_goals simp_all
  subst h1
  exact Fin.elim0 i
  all_goals rename_i h3
  all_goals rw [Fin.ext_iff] at h3
  all_goals simp_all
  all_goals omega

lemma basis_on_δ₂_self (j : Fin n) : basisAsCharges j (δ₂ j) = - 1 := by
  rw [basis_δ₂_eq_minus_δ₁, basis_on_δ₁_self]

lemma basis!_on_δ!₂_self (j : Fin n) : basis!AsCharges j (δ!₂ j) = - 1 := by
  rw [basis!_δ!₂_eq_minus_δ!₁, basis!_on_δ!₁_self]

lemma basis_on_δ₂_other {k j : Fin n} (h : k ≠ j) : basisAsCharges k (δ₂ j) = 0 := by
  rw [basis_δ₂_eq_minus_δ₁, basis_on_δ₁_other h]
  rfl

lemma basis!_on_δ!₂_other {k j : Fin n} (h : k ≠ j) : basis!AsCharges k (δ!₂ j) = 0 := by
  rw [basis!_δ!₂_eq_minus_δ!₁, basis!_on_δ!₁_other h]
  rfl

lemma basis_on_δ₃ (j : Fin n) : basisAsCharges j δ₃ = 0 := by
  simp [basisAsCharges]
  split <;> rename_i h
  rw [Fin.ext_iff] at h
  simp [δ₃, δ₁] at h
  omega
  split <;> rename_i h2
  rw [Fin.ext_iff] at h2
  simp [δ₃, δ₂] at h2
  omega
  rfl

lemma basis!_on_δ!₃ (j : Fin n) : basis!AsCharges j δ!₃ = 0 := by
  simp [basis!AsCharges]
  split <;> rename_i h
  rw [Fin.ext_iff] at h
  simp [δ!₃, δ!₁] at h
  omega
  split <;> rename_i h2
  rw [Fin.ext_iff] at h2
  simp [δ!₃, δ!₂] at h2
  omega
  rfl

def P (f : Fin n → ℚ) : (PureU1 (2 * n + 1)).charges := ∑ i, f i • basisAsCharges i

def P! (f : Fin n → ℚ) : (PureU1 (2 * n + 1)).charges := ∑ i, f i • basis!AsCharges i

def Pa (f : Fin n → ℚ) (g : Fin n → ℚ) : (PureU1 (2 * n + 1)).charges := P f + P! g

lemma P_δ₁ (f : Fin n → ℚ) (j : Fin n) : P f (δ₁ j) = f j := by
  rw [P, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  rw [basis_on_δ₁_self]
  simp
  intro k _ hkj
  rw [basis_on_δ₁_other hkj]
  simp only [mul_zero]
  simp only [mem_univ, not_true_eq_false, _root_.mul_eq_zero, IsEmpty.forall_iff]

lemma P!_δ!₁ (f : Fin n → ℚ)  (j : Fin n) : P! f (δ!₁ j) = f j := by
  rw [P!, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  rw [basis!_on_δ!₁_self]
  simp
  intro k _ hkj
  rw [basis!_on_δ!₁_other hkj]
  simp only [mul_zero]
  simp only [mem_univ, not_true_eq_false, _root_.mul_eq_zero, IsEmpty.forall_iff]

lemma P_δ₂ (f : Fin n → ℚ) (j : Fin n) : P f (δ₂ j) = - f j := by
  rw [P, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  rw [basis_on_δ₂_self]
  simp
  intro k _ hkj
  rw [basis_on_δ₂_other hkj]
  simp
  simp

lemma P!_δ!₂ (f : Fin n → ℚ) (j : Fin n) : P! f (δ!₂ j) = - f j := by
  rw [P!, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  rw [basis!_on_δ!₂_self]
  simp
  intro k _ hkj
  rw [basis!_on_δ!₂_other hkj]
  simp
  simp

lemma P_δ₃ (f : Fin n → ℚ) : P f (δ₃) = 0 := by
  rw [P, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul, basis_on_δ₃]

lemma P!_δ!₃ (f : Fin n → ℚ) : P! f (δ!₃) = 0 := by
  rw [P!, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul, basis!_on_δ!₃]


end VectorLikeOddPlane

end PureU1
