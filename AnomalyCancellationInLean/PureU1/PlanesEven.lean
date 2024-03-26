/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.PureU1.Basic
import AnomalyCancellationInLean.PureU1.Permutations
import Mathlib.Tactic.Polyrith
import Mathlib.RepresentationTheory.Basic

-- https://arxiv.org/pdf/1912.04804.pdf

namespace PureU1

open BigOperators

variable {n : ℕ}

namespace EvenBasis

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

lemma sum_of_charges {n : ℕ} (f : Fin k → (PureU1 n).charges) (j : Fin n) :
    (∑ i : Fin k, (f i)) j = (∑ i : Fin k, (f i) j) := by
  induction k
  simp
  rename_i k l hl
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hlt := hl (f ∘ Fin.castSucc)
  erw [← hlt]
  simp

namespace plane₁

lemma n_plus_n_eq_2n (n : ℕ) : n.succ + n.succ = 2 * n.succ := (Nat.two_mul n.succ).symm

def asCharges (j : Fin n.succ) : (PureU1 (2 * n.succ)).charges :=
  fun i =>
  if i = Fin.cast (n_plus_n_eq_2n n) (Fin.castAdd n.succ j) then
    1
  else
    if i = Fin.cast (n_plus_n_eq_2n n) (Fin.natAdd n.succ j) then
      - 1
    else
      0

lemma asCharges_on_castAdd (j : Fin n.succ) : asCharges j
    (Fin.cast (n_plus_n_eq_2n n) (Fin.castAdd n.succ j)) = 1 := by
  simp [asCharges]

lemma asCharges_on_castAdd_other {k j : Fin n.succ} (h : k ≠ j) :
    asCharges k (Fin.cast (n_plus_n_eq_2n n)  (Fin.castAdd n.succ j)) = 0 := by
  simp [asCharges]
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

lemma asCharages_natAdd_eq_minus_castAdd (j i : Fin n.succ) :
    asCharges j (Fin.cast (n_plus_n_eq_2n n)  (Fin.natAdd n.succ i)) = -
    asCharges j (Fin.cast (n_plus_n_eq_2n n)  (Fin.castAdd n.succ i)) := by
  simp [asCharges]
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

lemma sum_cast_index (j : Fin n.succ) :  ∑ i : Fin (2 * Nat.succ n), asCharges j i =
    ∑ i : Fin (n.succ + n.succ), asCharges j (Fin.cast (n_plus_n_eq_2n n) i)  := by
  rw [Finset.sum_equiv (Fin.castIso (n_plus_n_eq_2n n)).symm.toEquiv]
  intro i
  simp
  intro i _
  simp

@[simps!]
def asAnomalyFreeLinear (j : Fin n.succ) : (PureU1 (2 * n.succ)).AnomalyFreeLinear :=
  ⟨asCharges j, by
    intro i
    simp at i
    match i with
    | 0 =>
    simp only [PureU1_charges, Fin.isValue, PureU1_linearACCs, accGrav, PureU1Charges_charges,
      LinearMap.coe_mk, AddHom.coe_mk]
    rw [sum_cast_index j]
    rw [Fin.sum_univ_add]
    rw [← Finset.sum_add_distrib]
    simp [asCharages_natAdd_eq_minus_castAdd]
    ⟩

lemma linearlyIndependent : LinearIndependent ℚ (@asAnomalyFreeLinear n) := by
  apply Fintype.linearIndependent_iff.mpr
  intro g h j
  have h1 (i : Fin (2 * n.succ)) : ∑ k : Fin n.succ, ((g k • asAnomalyFreeLinear k).val i) = 0 := by
    rw [← sum_of_vectors, h]
    simp
    rfl
  have h2j := h1 (Fin.cast (n_plus_n_eq_2n n) (Fin.castAdd n.succ j))
  simp [HSMul.hSMul, SMul.smul] at h2j
  rw [Finset.sum_eq_single j] at h2j
  rw [asCharges_on_castAdd] at h2j
  simp_all
  intro k _ hkj
  rw [asCharges_on_castAdd_other hkj]
  simp
  simp



theorem accCube (g : Fin n.succ → ℚ) :
    (PureU1 (2 * n.succ)).cubicACC.toFun (∑ i, g i • asAnomalyFreeLinear i).val = 0 := by
  simp
  have h :
      ∑ i : Fin (2 * Nat.succ n), (∑ i : Fin (Nat.succ n), g i • asAnomalyFreeLinear i).val i ^ 3 =
      ∑ i : Fin (n.succ + n.succ), (∑ i : Fin (Nat.succ n), g i • asAnomalyFreeLinear i).val
      (Fin.cast (n_plus_n_eq_2n n) i) ^ 3 := by
    rw [Finset.sum_equiv (Fin.castIso (n_plus_n_eq_2n n)).symm.toEquiv]
    intro i
    simp
    intro i _
    simp
  rw [h]
  rw [Fin.sum_univ_add]
  rw [← Finset.sum_add_distrib]
  simp [sum_of_vectors, sum_of_vectors, HSMul.hSMul, SMul.smul]
  simp [asCharages_natAdd_eq_minus_castAdd]
  apply Finset.sum_eq_zero
  intro i _
  ring

@[simp]
def cond (S :  (PureU1 (2 * n.succ)).charges) : Prop :=
  ∀ (i : Fin n.succ), S (Fin.cast (n_plus_n_eq_2n n)  (Fin.castAdd n.succ i)) =
    - S (Fin.cast (n_plus_n_eq_2n n)  (Fin.natAdd n.succ i))

theorem cond_span (g : Fin n.succ → ℚ) :
    cond (∑ i, g i • asAnomalyFreeLinear i).val := by
  simp [cond]
  intro i
  rw [sum_of_vectors]
  simp [sum_of_vectors, sum_of_vectors, HSMul.hSMul, SMul.smul]
  simp [asCharages_natAdd_eq_minus_castAdd]

def P (g : Fin n.succ → ℚ) : (PureU1 (2 * Nat.succ n)).charges := (∑ i, g i • plane₁.asCharges i)

lemma sum_on_castAdd (f : Fin n.succ → ℚ) (j : Fin n.succ) : P f
   (Fin.cast (n_plus_n_eq_2n n)  (Fin.castAdd n.succ j)) = f j := by
  rw [P, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  rw [asCharges_on_castAdd]
  simp
  intro k _ hkj
  rw [asCharges_on_castAdd_other hkj]
  simp
  simp

lemma sum_on_natAdd (f : Fin n.succ → ℚ) (j : Fin n.succ):  P f
    (Fin.cast (n_plus_n_eq_2n n)  (Fin.natAdd n.succ j)) = - f j := by
  rw [P, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul]
  simp [asCharages_natAdd_eq_minus_castAdd]
  rw [Finset.sum_eq_single j]
  rw [asCharges_on_castAdd]
  simp
  intro k _ hkj
  rw [asCharges_on_castAdd_other hkj]
  simp
  simp

end plane₁

namespace plane₂


lemma n_cond₂ (n : ℕ) : 1 + ((n + n) + 1) = 2 * n.succ := by
  linarith


def asCharges (j : Fin n) : (PureU1 (2*n.succ)).charges :=
  fun i =>
  if i =  Fin.cast (n_cond₂ n)  (Fin.natAdd 1 (Fin.castAdd 1 (Fin.castAdd n j))) then
    1
  else
    if i =  Fin.cast (n_cond₂ n) (Fin.natAdd 1 (Fin.castAdd 1 (Fin.natAdd n j))) then
      -1
    else

      0

lemma asCharges_on_zero (j : Fin n) :
    asCharges j (Fin.cast (n_cond₂ n) (Fin.castAdd ( n +  n + 1) 0)) = 0 := by
  simp [asCharges]
  split <;> rename_i h1
  rw [Fin.ext_iff] at h1
  simp at h1
  omega
  split <;> rename_i h2
  rw [Fin.ext_iff] at h1 h2
  simp_all
  omega
  rfl

lemma asCharges_on_last (j : Fin n) :
    asCharges j (Fin.cast (n_cond₂ n) (Fin.natAdd 1 (Fin.natAdd ( n + n) 0))) = 0 := by
  simp [asCharges]
  split <;> rename_i h1
  rw [Fin.ext_iff] at h1
  simp at h1
  omega
  split <;> rename_i h2
  rw [Fin.ext_iff] at h1 h2
  simp_all
  omega
  rfl

lemma asCharges_on_castAdd (j : Fin n) :
    asCharges j (Fin.cast (n_cond₂ n)
    (Fin.natAdd 1 (Fin.castAdd 1 (Fin.castAdd n j)))) = 1 := by
  simp [asCharges]

lemma asCharges_on_castAdd_other {k j : Fin n} (h : k ≠ j) :
    asCharges k (Fin.cast (n_cond₂ n) (Fin.natAdd 1 (Fin.castAdd 1 (Fin.castAdd n j)))) = 0 := by
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

lemma asCharges_on_other (j : Fin n) (i : Fin (2*n.succ))
    (h1 : i ≠ (Fin.cast (n_cond₂ n) (Fin.natAdd 1 (Fin.castAdd 1 (Fin.castAdd n j)))))
    (h2 : i ≠ (Fin.cast (n_cond₂ n) (Fin.natAdd 1 (Fin.castAdd 1 (Fin.natAdd n j)))) ) :
    asCharges j i = 0 := by
  simp [asCharges]
  split
  simp_all
  rfl

lemma asCharges_natAdd_eq_minus_castAdd (j  : Fin n) (i : Fin n) :
    asCharges j (Fin.cast (n_cond₂ n)
      (Fin.natAdd 1 (Fin.castAdd 1 (Fin.natAdd (n) i))))= -
    asCharges j (Fin.cast (n_cond₂ n)
      (Fin.natAdd 1 (Fin.castAdd 1 (Fin.castAdd (n) i)))) := by
  simp [asCharges]
  split <;> split
  any_goals split
  any_goals split
  any_goals rfl
  all_goals rename_i h1 h2
  all_goals rw [Fin.ext_iff] at h1 h2
  all_goals simp_all
  omega
  all_goals rename_i h3
  all_goals rw [Fin.ext_iff] at h3
  all_goals simp_all
  all_goals omega

def P (f : Fin n → ℚ) : (PureU1 (2 * Nat.succ n)).charges := (∑ i, f i • plane₂.asCharges i)

lemma sum_on_castAdd (f : Fin n → ℚ) (j : Fin n):  P f (Fin.cast (n_cond₂ n)
    (Fin.natAdd 1 (Fin.castAdd 1 (Fin.castAdd n j)))) = f j := by
  rw [P, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul]
  rw [Finset.sum_eq_single j]
  rw [asCharges_on_castAdd]
  simp
  intro k _ hkj
  rw [asCharges_on_castAdd_other hkj]
  simp
  simp

lemma sum_on_zero (f : Fin n → ℚ) :  P f 0 = 0 := by
  rw [P, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul]
  have h : (Fin.cast (n_cond₂ n) (Fin.castAdd ( n +  n + 1) 0)) = 0 := by
    rw [Fin.ext_iff]
    simp
  rw [← h]
  simp [asCharges_on_zero]

lemma sum_on_last (f : Fin n → ℚ) :  P f (Fin.last (2 * n.succ -1))
     = 0 := by
  rw [P, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul]
  have h : (Fin.cast (n_cond₂ n) (Fin.natAdd 1 (Fin.natAdd (n + n) 0)))
   =  (Fin.last (2 * n.succ -1)) := by
    rw [Fin.ext_iff]
    simp
    omega
  rw [← h]
  simp [asCharges_on_last]

lemma sum_on_natAdd (f : Fin n → ℚ) (j : Fin n)  : P f (Fin.cast (n_cond₂ n)
    (Fin.natAdd 1 (Fin.castAdd 1 (Fin.natAdd n j)))) = - f j := by
  rw [P, sum_of_charges]
  simp [HSMul.hSMul, SMul.smul]
  simp [asCharges_natAdd_eq_minus_castAdd]
  rw [Finset.sum_eq_single j]
  rw [asCharges_on_castAdd]
  simp
  intro k _ hkj
  rw [asCharges_on_castAdd_other hkj]
  simp
  simp

end plane₂

lemma cast_planes_castAdd (j : Fin n) :
    Fin.cast (plane₂.n_cond₂ n) (Fin.natAdd 1 (Fin.castAdd 1 (Fin.castAdd n j)))
    =  Fin.cast (plane₁.n_plus_n_eq_2n n) (Fin.castAdd n.succ j.succ) := by
  rw [Fin.ext_iff]
  simp
  ring

lemma cast_planes_natAdd (j : Fin n) :
    Fin.cast (plane₂.n_cond₂ n) (Fin.natAdd 1 (Fin.castAdd 1 (Fin.natAdd n j)))
    =  Fin.cast (plane₁.n_plus_n_eq_2n n) (Fin.natAdd n.succ j.castSucc) := by
  rw [Fin.ext_iff]
  simp
  ring_nf
  rw [Nat.succ_eq_add_one]
  ring


section coordinates


lemma f_in_terms_of_g (g : Fin n.succ → ℚ) (f : Fin n → ℚ)
    {S : (PureU1 (2 * n.succ)).AnomalyFreeLinear}
    (h : S.val = plane₁.P g + plane₂.P f)
    (j : Fin n) :
    f j = - g j.castSucc
    - S.val (Fin.cast (plane₁.n_plus_n_eq_2n n) (Fin.natAdd n.succ j.castSucc)) := by
  rw [h]
  simp only [PureU1_charges, Pi.add_apply]
  nth_rewrite 2 [← cast_planes_natAdd]
  rw [plane₂.sum_on_natAdd]
  rw [plane₁.sum_on_natAdd]
  ring

lemma g_in_terms_of_f  (g : Fin n.succ → ℚ) (f : Fin n → ℚ)
    {S : (PureU1 (2 * n.succ)).AnomalyFreeLinear}
    (h : S.val = plane₁.P g + plane₂.P f) (j : Fin n) :
    g j.succ = S.val (Fin.cast (plane₁.n_plus_n_eq_2n n) (Fin.castAdd n.succ j.succ)) - f j := by
  rw [h]
  simp only [PureU1_charges, Pi.add_apply]
  rw [plane₁.sum_on_castAdd]
  rw [← cast_planes_castAdd]
  rw [plane₂.sum_on_castAdd]
  ring

lemma g_succ_minus_g (g : Fin n.succ → ℚ) (f : Fin n → ℚ)
    {S : (PureU1 (2 * n.succ)).AnomalyFreeLinear}
    (h : S.val = plane₁.P g + plane₂.P f) (j : Fin n) :
    g j.succ - g j.castSucc =
      S.val (Fin.cast (plane₁.n_plus_n_eq_2n n) (Fin.castAdd n.succ j.succ)) +
      S.val (Fin.cast (plane₁.n_plus_n_eq_2n n) (Fin.natAdd n.succ j.castSucc)) := by
  rw [g_in_terms_of_f g f h]
  rw [f_in_terms_of_g g f h]
  ring

lemma g_zero (g : Fin n.succ → ℚ) (f : Fin n → ℚ)
    {S : (PureU1 (2 * n.succ)).AnomalyFreeLinear}
    (h : S.val = plane₁.P g + plane₂.P f) :
     g 0 = S.val 0 := by
  rw [h]
  simp only [PureU1_charges, Pi.add_apply]
  rw [plane₂.sum_on_zero]
  have h : 0 = (Fin.cast (plane₁.n_plus_n_eq_2n n) (Fin.castAdd n.succ 0)):= by
    rw [Fin.ext_iff]
    simp
  rw [h]
  rw [plane₁.sum_on_castAdd]
  simp

lemma g_last (g : Fin n.succ → ℚ) (f : Fin n → ℚ)
    {S : (PureU1 (2 * n.succ)).AnomalyFreeLinear}
    (h : S.val = plane₁.P g + plane₂.P f) :
     g (Fin.last n) = - S.val (Fin.last (2 * n.succ -1)) := by
  rw [h]
  simp only [PureU1_charges, Pi.add_apply, neg_add_rev]
  rw [plane₂.sum_on_last]
  have h : (Fin.last (2 * Nat.succ n - 1)) =
       (Fin.cast (plane₁.n_plus_n_eq_2n n) (Fin.natAdd n.succ (Fin.last n))):= by
    rw [Fin.ext_iff]
    simp
    omega
  rw [h]
  rw [plane₁.sum_on_natAdd]
  simp

lemma g_last' (g : Fin n.succ.succ → ℚ) (f : Fin n.succ → ℚ)
    {S : (PureU1 (2 * n.succ.succ)).AnomalyFreeLinear}
    (h : S.val = plane₁.P g + plane₂.P f) :
     g (Fin.last n).succ = - S.val (Fin.last (2 * n.succ )).succ := by
  have h1 : (Fin.last n).succ = Fin.last n.succ := by
    rfl
  rw [h1]
  erw [g_last g f h]
  rfl

end coordinates

lemma line_in_cubic_p1_p1_p2 (g : Fin n.succ → ℚ) (f : Fin n → ℚ)
    (h : ∀ (a b : ℚ), (PureU1.accCube (2 * n.succ)).toFun (a • plane₁.P g + b • plane₂.P f) = 0) :
    accCubeTriLinSymm.toFun (plane₁.P g, plane₁.P g, plane₂.P f) = 0 := by
  rw [accCube_from_tri] at h
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

lemma span_basis (S : (PureU1 (2 * n.succ)).AnomalyFreeLinear) :
    ∃ (g : Fin n.succ → ℚ) (f : Fin n → ℚ), S.val = plane₁.P g + plane₂.P f := by
  sorry

def lineInCubic (S : (PureU1 (2 * n.succ)).AnomalyFreeLinear) : Prop :=
  ∀ (g : Fin n.succ → ℚ) (f : Fin n → ℚ) (_ : S.val =  plane₁.P g + plane₂.P f) (a b : ℚ) ,
  (PureU1.accCube (2 * n.succ)).toFun (a • plane₁.P g + b • plane₂.P f) = 0

lemma lineInCubic_p1_p1_p2 (S : (PureU1 (2 * n.succ)).AnomalyFreeLinear)
    (hS : lineInCubic S) :
    ∀ (g : Fin n.succ → ℚ) (f : Fin n → ℚ) (_ : S.val =  plane₁.P g + plane₂.P f),
    accCubeTriLinSymm.toFun (plane₁.P g, plane₁.P g, plane₂.P f) = 0 := by
  intro g f h
  exact line_in_cubic_p1_p1_p2 g f (hS g f h )


def lineInCubicPerm (S : (PureU1 (2 * n.succ)).AnomalyFreeLinear) : Prop :=
  ∀ (M : (FamilyPermutations (2 * n.succ)).group ),
    lineInCubic ((FamilyPermutations (2 * n.succ)).repAnomalyFreeLinear M S)

lemma lineInCubicPerm_self (S : (PureU1 (2 * n.succ)).AnomalyFreeLinear)
    (hS : lineInCubicPerm S) : lineInCubic S := by
  exact hS 1

lemma lineInCubicPerm_permute (S : (PureU1 (2 * n.succ)).AnomalyFreeLinear)
    (hS : lineInCubicPerm S) (M' : (FamilyPermutations (2 * n.succ)).group) :
    lineInCubicPerm ((FamilyPermutations (2 * n.succ)).repAnomalyFreeLinear M' S) := by
  rw [lineInCubicPerm]
  intro M
  have ht : (((ACCSystemGroupAction.repAnomalyFreeLinear (FamilyPermutations (2 * Nat.succ n))) M)
    (((ACCSystemGroupAction.repAnomalyFreeLinear (FamilyPermutations (2 * Nat.succ n))) M') S))
    = (ACCSystemGroupAction.repAnomalyFreeLinear (FamilyPermutations (2 * Nat.succ n))) (M * M') S
      := by
    simp [(FamilyPermutations (2 * n.succ)).repAnomalyFreeLinear.map_mul']
  rw [ht]
  exact hS (M * M')

@[simps!]
def MSwapI1 : Fin (2 * n.succ.succ)  :=  Fin.cast (plane₂.n_cond₂ n.succ)
  (Fin.natAdd 1 (Fin.castAdd 1 (Fin.castAdd n.succ (Fin.last n))))


@[simps!]
def MSwapI2 : Fin (2 * n.succ.succ)  :=  Fin.cast (plane₂.n_cond₂ n.succ)
  (Fin.natAdd 1 (Fin.castAdd 1 (Fin.natAdd n.succ (Fin.last n))))

def MSwap : (FamilyPermutations (2 * n.succ.succ)).group where
  toFun i :=
    if i = MSwapI1 then
        MSwapI2
    else
      if i = MSwapI2 then
        MSwapI1
      else
        i
  invFun i :=
    if i = MSwapI1 then
        MSwapI2
    else
      if i = MSwapI2 then
        MSwapI1
      else
        i
  left_inv i := by
    aesop
  right_inv i := by
    aesop

lemma MSwap_inv_on_I1 : (@MSwap n).invFun MSwapI1  = MSwapI2 := by
  simp [MSwap]

lemma MSwap_inv_on_I2 : (@MSwap n).invFun MSwapI2  = MSwapI1 := by
  simp [MSwap]

lemma MSwap_inv_on_not_I1_or_i2 {i : Fin (2 * n.succ.succ)}
    (h1 : i ≠ MSwapI1) (h2 : i ≠ MSwapI2):
    (@MSwap n).invFun i = i := by
  simp [MSwap]
  split
  simp_all
  rfl

lemma MSwap_add {S S' : (PureU1 (2 * n.succ.succ)).AnomalyFreeLinear}
    (hS : ((FamilyPermutations (2 * n.succ.succ)).repAnomalyFreeLinear MSwap S) = S') :
    S'.val = S.val + (S.val MSwapI2 - S.val MSwapI1) • plane₂.asCharges (Fin.last n) := by
  funext i
  simp
  rw [← hS]
  rw [ACCSystemGroupAction.repAnomalyFreeLinear]
  simp
  rw [ACCSystemGroupAction.anomalyFreeLinearMap]
  simp
  erw [FamilyPermutations_charges_apply]
  by_cases  hi : i = MSwapI1
  subst hi
  erw [plane₂.asCharges_on_castAdd]
  rw [MSwap_inv_on_I1]
  simp
  by_cases hi2 : i = MSwapI2
  subst hi2
  erw [plane₂.asCharges_natAdd_eq_minus_castAdd]
  erw [plane₂.asCharges_on_castAdd]
  rw [MSwap_inv_on_I2]
  simp
  rw [MSwap_inv_on_not_I1_or_i2 hi hi2]
  rw [plane₂.asCharges_on_other _ _ hi hi2]
  simp


lemma accCubeTriLin_plane₁_plane₁ (g : Fin n.succ.succ → ℚ) (j : Fin n.succ) :
    accCubeTriLinSymm.toFun (plane₁.P g, plane₁.P g, plane₂.asCharges j)
    = g (Fin.succ j) ^ 2 - g (Fin.castSucc j) ^ 2 := by
  rw [accCubeTriLinSymm_cast (plane₂.n_cond₂ n.succ) _]
  rw [Fin.sum_univ_add]
  rw [Fin.sum_univ_add]
  rw [Fin.sum_univ_add]
  simp
  rw [plane₂.asCharges_on_zero, plane₂.asCharges_on_last]
  simp
  rw [← Finset.sum_add_distrib]
  simp only [plane₂.asCharges_natAdd_eq_minus_castAdd]
  simp
  rw [Finset.sum_eq_single j]
  rw [plane₂.asCharges_on_castAdd]
  simp
  rw [cast_planes_castAdd, cast_planes_natAdd]
  rw [plane₁.sum_on_castAdd, plane₁.sum_on_natAdd]
  simp
  ring
  intro k _ hjk
  rw [plane₂.asCharges_on_castAdd_other hjk.symm]
  simp
  simp


@[simps!]
def v_i1 : Fin (2 * n.succ.succ) := (Fin.cast (plane₁.n_plus_n_eq_2n n.succ)
   (Fin.castAdd (Nat.succ (n + 1)) (Fin.succ (Fin.last n))))

@[simps!]
def v_i2 : Fin (2 * n.succ.succ) :=  (Fin.cast (plane₁.n_plus_n_eq_2n n.succ)
   (Fin.natAdd (Nat.succ (n + 1)) (Fin.castSucc (Fin.last n))))

@[simps!]
def MSwapI3 : Fin (2 * n.succ.succ) := (Fin.succ (Fin.last (2 * Nat.succ n)))

lemma v1_MSwapI1 : @v_i1 n = MSwapI1 := by
  simp [v_i1, MSwapI1]
  rw [Fin.ext_iff]
  simp
  omega

lemma v2_MSwapI1 : @v_i2 n = MSwapI2 := by
  simp [v_i2, MSwapI2]
  rw [Fin.ext_iff]
  simp
  omega

def MSwapTriple {i j k : Fin (2 * n.succ.succ)} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (FamilyPermutations (2 * n.succ.succ)).group where
  toFun s :=
    if s = i then
        MSwapI1
    else
      if s = j then
        MSwapI2
      else
        if s = k then
          MSwapI3
        else
          s
  invFun s :=
    if s = MSwapI1 then
        i
    else
      if s = MSwapI2 then
        j
      else
        if s = MSwapI3 then
          k
        else
          s
  left_inv s := by
    sorry
  right_inv s := by
    sorry

lemma MSwapTriple_inv_MSwapI1 {i j k : Fin (2 * n.succ.succ)} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : (MSwapTriple hij hik hjk).invFun MSwapI1 = i := by
  simp [MSwapTriple]


lemma MSwapTriple_inv_MSwapI2 {i j k : Fin (2 * n.succ.succ)} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : (MSwapTriple hij hik hjk).invFun MSwapI2 = j := by
  simp [MSwapTriple]
  intro h
  simp [MSwapI2, MSwapI1] at h
  rw [Fin.ext_iff] at h
  simp at h


lemma MSwapTriple_inv_MSwapI3 {i j k : Fin (2 * n.succ.succ)} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : (MSwapTriple hij hik hjk).invFun MSwapI3 = k := by
  simp [MSwapTriple]
  split
  rename_i h
  simp [MSwapI2, MSwapI1] at h
  rw [Fin.ext_iff] at h
  simp at h
  omega
  split
  rename_i h1 h2
  simp [MSwapI2, MSwapI1] at h2
  rw [Fin.ext_iff] at h2
  simp at h2
  omega
  rfl

lemma accCubeTriLin_plane₁_plane₁_last  (g : Fin n.succ.succ → ℚ) (f : Fin n.succ → ℚ)
    {S : (PureU1 (2 * n.succ.succ)).AnomalyFreeLinear}
    (h : S.val = plane₁.P g + plane₂.P f) :
    accCubeTriLinSymm.toFun (plane₁.P g, plane₁.P g, plane₂.asCharges (Fin.last n))
    = - (S.val MSwapI1 + S.val MSwapI2) *  (2 * S.val MSwapI3 + S.val MSwapI1 +S.val MSwapI2)
      := by
  rw [accCubeTriLin_plane₁_plane₁]
  have  h1 : g (Fin.succ (Fin.last n)) ^ 2 - g (Fin.castSucc (Fin.last n)) ^ 2
      = (g (Fin.succ (Fin.last n)) -  g (Fin.castSucc (Fin.last n))) *
        (2 * g (Fin.succ (Fin.last n)) - ( g (Fin.succ (Fin.last n))- g (Fin.castSucc (Fin.last n))))  := by
    ring
  rw [h1]
  rw [g_succ_minus_g g f h]
  rw [g_last' g f h]
  rw [← v1_MSwapI1, ← v2_MSwapI1]
  rw [v_i1, v_i2, MSwapI3]
  ring

lemma MSwap_cond_single {S  : (PureU1 (2 * n.succ.succ)).AnomalyFreeLinear}
    (LSP : lineInCubicPerm S) :
    (S.val MSwapI1 - S.val MSwapI2) * (S.val MSwapI1 + S.val MSwapI2) *
    (2 * S.val MSwapI3 + S.val MSwapI1 + S.val MSwapI2) = 0 := by
  let S' :=  (FamilyPermutations (2 * n.succ.succ)).repAnomalyFreeLinear MSwap S
  have hSS' : ((FamilyPermutations (2 * n.succ.succ)).repAnomalyFreeLinear MSwap S) = S' := rfl
  have LS' := LSP MSwap
  rw [hSS'] at LS'
  have LS := lineInCubicPerm_self S LSP
  obtain ⟨g, f, hS⟩ := span_basis S
  have hn := MSwap_add hSS'
  have hx : S'.val = plane₁.P g +
    (plane₂.P f + (S.val MSwapI2 - S.val MSwapI1) • plane₂.asCharges (Fin.last n)) := by
    rw [hn]
    rw [← add_assoc]
    simp
    exact hS
  let X := plane₂.P f + (S.val MSwapI2 - S.val MSwapI1) • plane₂.asCharges (Fin.last n)
  have hf : plane₂.P f ∈ Submodule.span ℚ (Set.range (plane₂.asCharges)) := by
     rw [(mem_span_range_iff_exists_fun ℚ)]
     use f
     rfl
  have hP : (S.val MSwapI2 - S.val MSwapI1) • plane₂.asCharges (Fin.last n) ∈
      Submodule.span ℚ (Set.range (plane₂.asCharges)) := by
    apply Submodule.smul_mem
    apply SetLike.mem_of_subset
    apply Submodule.subset_span
    simp_all only [Set.mem_range, exists_apply_eq_apply]
  have hX : X ∈  Submodule.span ℚ (Set.range (plane₂.asCharges)) := by
    apply Submodule.add_mem
    exact hf
    exact hP
  have hXsum := (mem_span_range_iff_exists_fun ℚ).mp hX
  obtain ⟨f', hf'⟩ := hXsum
  simp only [X] at hf'
  erw [← hf'] at  hx
  change S'.val = plane₁.P g + plane₂.P f' at hx
  have ht := lineInCubic_p1_p1_p2 S' LS' g f' hx
  have ht2 := lineInCubic_p1_p1_p2 S LS g f hS
  change plane₂.P f'  = _ at hf'
  erw [hf'] at ht
  rw [accCubeTriLinSymm.map_add₃, accCubeTriLinSymm.map_smul₃] at ht
  rw [ht2] at ht
  simp only [zero_add] at ht
  rw [accCubeTriLin_plane₁_plane₁_last g f hS] at ht
  have hl:  (S.val MSwapI2 - S.val MSwapI1) * (-(S.val MSwapI1 + S.val MSwapI2) *
    (2 * S.val MSwapI3 + S.val MSwapI1 + S.val MSwapI2)) =
     (S.val MSwapI1 - S.val MSwapI2) * (S.val MSwapI1 + S.val MSwapI2) *
    (2 * S.val MSwapI3 + S.val MSwapI1 + S.val MSwapI2) := by
    ring
  rw [hl] at ht
  exact ht


lemma MSwap_cond {S  : (PureU1 (2 * n.succ.succ)).AnomalyFreeLinear}
    (LSP : lineInCubicPerm S) :
    ∀ (i1 i2 i3 : Fin ((2 * n.succ) + 1 + 1)) (_ : i1 ≠ i2) (_ : i2 ≠ i3) (_ : i1 ≠ i3),
    S.val i1 = S.val i2 ∨ S.val i1 = - S.val i2 ∨ 2 * S.val i3 + S.val i1 + S.val i2 = 0 := by
  intro i j k hij hjk hik
  let S' := (FamilyPermutations (2 * n.succ.succ)).repAnomalyFreeLinear
    (MSwapTriple hij hik hjk) S
  have LSP' : lineInCubicPerm S' := lineInCubicPerm_permute S LSP (MSwapTriple hij hik hjk)
  have C := MSwap_cond_single LSP'
  simp only [mul_eq_zero, S'] at C
  rw [ACCSystemGroupAction.repAnomalyFreeLinear] at C
  simp at C
  rw [ACCSystemGroupAction.anomalyFreeLinearMap] at C
  simp at C
  erw [FamilyPermutations_charges_apply] at C
  erw [FamilyPermutations_charges_apply] at C
  erw [FamilyPermutations_charges_apply] at C
  rw [MSwapTriple_inv_MSwapI1] at C
  rw [MSwapTriple_inv_MSwapI2] at C
  rw [MSwapTriple_inv_MSwapI3] at C
  have h1 :  (S.val i = S.val j) ↔ (S.val i - S.val j = 0) := by
    apply Iff.intro
    intro h
    linarith
    intro h
    linarith
  have h2 :  (S.val i = - S.val j) ↔ (S.val i + S.val j = 0) := by
    apply Iff.intro
    intro h
    linarith
    intro h
    linarith
  rw [h1, h2]
  rw [← or_assoc]
  exact C










section permutation




-- (S.val V_i1 - S.val V_i2) * (S.val v_i1 + S.val v_i2) *
-- (2 * S.val v_i3 + S.val v_i1 + S.val v_i2)
namespace appendixCond

def cond (S : (PureU1 (n)).AnomalyFreeLinear) : Prop :=
  ∀ (i1 i2 i3 : Fin (n)) (_ : i1 ≠ i2) (_ : i2 ≠ i3) (_ : i1 ≠ i3),
  S.val i1 = S.val i2 ∨ S.val i1 = - S.val i2 ∨ 2 * S.val i3 + S.val i1 + S.val i2 = 0

lemma cond_implies {S : (PureU1 (n.succ.succ)).AnomalyFreeLinear} (hS : cond S)
   (h : ¬ (S.val ((Fin.last n).castSucc))^2 = (S.val ((Fin.last n).succ))^2 ) :
    (2 - n) * S.val (Fin.last (n + 1)) =
    - (2 - n)* S.val (Fin.castSucc (Fin.last n)) := by
  erw [sq_eq_sq_iff_eq_or_eq_neg] at h
  simp [not_or] at h
  have h1 (i : Fin n) : S.val i.castSucc.castSucc =
      - (S.val ((Fin.last n).castSucc) +  (S.val ((Fin.last n).succ))) / 2 := by
    have h1S := hS (Fin.last n).castSucc ((Fin.last n).succ) i.castSucc.castSucc
      (by simp; rw [Fin.ext_iff]; simp; omega)
      (by simp; rw [Fin.ext_iff]; simp; omega)
      (by simp; rw [Fin.ext_iff]; simp; omega)
    simp_all
    field_simp
    linear_combination h1S
  have h2 := pureU1_last S
  rw [Fin.sum_univ_castSucc] at h2
  simp [h1] at h2
  field_simp at h2
  linear_combination h2




lemma test_six₁ (S : (PureU1 ((2 * n.succ) + 1 + 1)).AnomalyFreeLinear) :
    S.val (Fin.last ((2 * n.succ) +  1)) =
    - ∑ i : Fin (2 * n.succ), S.val i.castSucc.castSucc  -
      S.val (Fin.castSucc (Fin.last (2 * n.succ))) := by
  rw [pureU1_last]
  rw [Fin.sum_univ_castSucc]
  ring

lemma test_six₂ (S : (PureU1 ((2 * n.succ) + 1 + 1)).AnomalyFreeLinear)
  (h123 : ∀ (i1 i2 i3 : Fin ((2 * n.succ) + 1 + 1)) (_ : i1 ≠ i2) (_ : i2 ≠ i3) (_ : i1 ≠ i3),
    S.val i1 = S.val i2 ∨ S.val i1 = - S.val i2 ∨
    2 * S.val i3 + S.val i1 + S.val i2 = 0)
    (hn1 : S.val ((Fin.last (2 * n.succ)).castSucc) ≠ S.val (Fin.last ((2 * n.succ) +  1)))
    (hn2 : S.val ((Fin.last (2 * n.succ)).castSucc) ≠ - S.val (Fin.last ((2 * n.succ) +  1))) :
    ∀ (i : Fin (2 * n.succ)), S.val i.castSucc.castSucc =
      - (S.val ((Fin.last (2 * n.succ)).castSucc) + S.val (Fin.last ((2 * n.succ) +  1))) / 2 := by
  intro i
  have t : i.castSucc.castSucc ≠ (Fin.last (2 * n.succ)).castSucc := by
      simp [Fin.castSucc_lt_last]
      have h := Fin.castSucc_lt_last i
      by_contra hn
      apply Fin.castSucc_injective at hn
      simp_all only [lt_self_iff_false]
  have t2 : i.castSucc.castSucc ≠ (Fin.last ((2 * n.succ) +  1)) := by
     have h := Fin.castSucc_lt_last i.castSucc
     by_contra hn
     simp_all only [lt_self_iff_false]
  have l := h123 (Fin.last (2 * n.succ)).castSucc (Fin.last ((2 * n.succ) +  1))
    i.castSucc.castSucc (by aesop) (t2.symm) (t.symm)
  cases l
  simp_all
  rename_i l
  cases l
  rename_i h
  simp_all
  rename_i h
  field_simp
  linear_combination h

lemma test_six₃ (S : (PureU1 ((2 * n.succ.succ) + 1 + 1)).AnomalyFreeLinear)
  (h123 : ∀ (i1 i2 i3 : Fin ((2 * n.succ.succ) + 1 + 1)) (_ : i1 ≠ i2) (_ : i2 ≠ i3) (_ : i1 ≠ i3),
    S.val i1 = S.val i2 ∨ S.val i1 = - S.val i2 ∨
    2 * S.val i3 + S.val i1 + S.val i2 = 0)
    (hn1 : S.val ((Fin.last (2 * n.succ.succ)).castSucc) ≠ S.val (Fin.last ((2 * n.succ.succ) +  1)))
    (hn2 : S.val ((Fin.last (2 * n.succ.succ)).castSucc) ≠ - S.val (Fin.last ((2 * n.succ.succ) +  1))) :
    False := by
  have h := test_six₁ S
  have h2 := test_six₂ S h123 hn1 hn2
  simp [h2] at h
  field_simp at h
  have h3 : ( - 2 * (↑n +1 )) * S.val (Fin.last ((2 * n.succ.succ) +  1))
      = - (- 2 * (↑n +1 )) * S.val ((Fin.last (2 * n.succ.succ)).castSucc) := by
      linear_combination h
  have h4 : - (2 : ℚ) * (↑n +1 ) ≠ 0 := by
    simp_all only [neg_mul, ne_eq, neg_eq_zero, _root_.mul_eq_zero, OfNat.ofNat_ne_zero, false_or]
    apply Not.intro
    intro a
    linarith
  have ht :  S.val (Fin.last ((2 * n.succ.succ) +  1))  =
    - S.val ((Fin.last (2 * n.succ.succ)).castSucc) := by
    rw [← mul_left_inj' h4]
    simp_all only [neg_mul]
    simpa [mul_comm] using h3
  simp_all


end appendixCond

end permutation

end EvenBasis
def basis₁ (j : Fin n) : (PureU1 (n + n)).charges :=
 (fun i =>
  if i = (Fin.castAdd n j) then
    1
  else
    if i = (Fin.natAdd n j) then
      - 1
    else
      0)

def basis₂ (j : Fin n) : (PureU1 (1 + ((n + n) + 1))).charges :=
  fun i =>
  if i = Fin.natAdd 1 (Fin.castAdd 1 (Fin.castAdd n j)) then
    1
  else
    if i = Fin.natAdd 1 (Fin.castAdd 1 (Fin.natAdd n j)) then
      -1
    else
      0



lemma basis₁_on_castAdd (j : Fin n) : basis₁ j (Fin.castAdd n j) = 1 := by
  simp [basis₁]

lemma basis₁_on_castAdd_other {k j : Fin n} (h : k ≠ j) :
    basis₁ k (Fin.castAdd n j) = 0 := by
  simp [basis₁]
  split
  rename_i h1
  rw [Fin.ext_iff] at h1
  simp_all
  rw [Fin.ext_iff] at h
  simp_all
  split
  rename_i h1 h2
  have hj : Fin.castAdd n j < n := by
    exact j.prop
  simp_all
  rfl

lemma basis₂_on_castAdd (j : Fin n) :
    basis₂ j (Fin.natAdd 1 (Fin.castAdd 1 (Fin.castAdd n j))) = 1 := by
  simp [basis₂]

lemma basis₂_on_castAdd_other {k j : Fin n} (h : k ≠ j) :
    basis₂ k (Fin.natAdd 1 (Fin.castAdd 1 (Fin.castAdd n j))) = 0 := by
  simp [basis₂]
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

lemma sum_of_vectors {n : ℕ} (f : Fin k → (PureU1 n).charges) (j : Fin n) :
    (∑ i : Fin k, f i) j = (∑ i : Fin k, f i j) := by
  induction k
  simp
  rename_i k l hl
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  have hlt := hl (f ∘ Fin.castSucc)
  erw [← hlt]
  simp

def basis₁_linearly_independent : LinearIndependent ℚ (@basis₁ n) := by
  apply Fintype.linearIndependent_iff.mpr
  intro g
  intro h
  intro j
  have h1 (i : Fin (n+n)) : (∑ k : Fin n, g k • basis₁ k) i = 0 := by
    rw [h]
    simp
  have h2 (i : Fin (n+n)) : (∑ k : Fin n, g k • basis₁ k) i =
      (∑ k : Fin n, (g k • (basis₁ k)) i)  := by
    exact sum_of_vectors (fun k => g k • basis₁ k) i
  simp [h1] at h2
  have h2j := h2  (Fin.castAdd n j)
  rw [Finset.sum_eq_single j] at h2j
  rw [basis₁_on_castAdd] at h2j
  simp_all
  intro k _ hkj
  rw [basis₁_on_castAdd_other hkj]
  simp
  simp

def Γ₁ₑCharges (S : (PureU1 (n + n)).charges) : Prop :=
  ∀ (i : Fin n), S (Fin.castAdd n i) = - S (Fin.natAdd n i)

lemma Γ₁ₑCharges_grav (S : (PureU1 (n + n)).charges)  (h : Γ₁ₑCharges S) :
    accGrav (n+n) S = 0 := by
  simp [accGrav]
  rw [Fin.sum_univ_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i
  rw [h i]
  simp

def Γ₂ₑCharges (S : (PureU1 (1 + ((n + n) + 1))).charges) : Prop :=
  S (Fin.castAdd ((n + n) + 1) (0 : Fin 1)) = 0 ∧
  S (Fin.natAdd 1 (Fin.natAdd (n + n) (0 : Fin 1))) = 0 ∧
  ∀ i, S (Fin.natAdd 1 (Fin.castAdd 1 (Fin.castAdd n i))) =
  - S (Fin.natAdd 1 (Fin.castAdd 1 (Fin.natAdd n i)))

section intersection

lemma n_plus_n_eq_2n (n : ℕ) : n.succ + n.succ = 2 * n.succ := (Nat.two_mul n.succ).symm

lemma n_cond₂ (n : ℕ) :1 + ((n + n) + 1) = 2 * n.succ := by
  linarith

@[simp]
def cond₁ (S :  (PureU1 (2 * n.succ)).charges) : Prop :=
  let S' := (pureU1_eq_charges (n_plus_n_eq_2n n)).invFun S
  ∀ (i : Fin n.succ), S' (Fin.castAdd n.succ i) = - S' (Fin.natAdd n.succ i)

@[simp]
def cond₂ (S :  (PureU1 (2 * n.succ)).charges) : Prop :=
  let S' := (pureU1_eq_charges (n_cond₂ n)).invFun S
  S' (Fin.castAdd ((n + n) + 1) (0 : Fin 1)) = 0 ∧
  S' (Fin.natAdd 1 (Fin.natAdd (n + n) (0 : Fin 1))) = 0 ∧
  ∀ i, S' (Fin.natAdd 1 (Fin.castAdd 1 (Fin.castAdd n i))) =
  - S' (Fin.natAdd 1 (Fin.castAdd 1 (Fin.natAdd n i)))

lemma fst_eq_zero (S :  (PureU1 (2 * n.succ)).charges) (hS2 :cond₂ S) :
    S 0 = 0 := by
  simp at hS2
  simpa using hS2.1

lemma n_eq_zero (S :  (PureU1 (2 * n.succ)).charges) (hS1 : cond₁ S) (hS2 :cond₂ S) :
    (S ∘ Fin.cast (n_plus_n_eq_2n n)) (Fin.natAdd n.succ 0 : Fin (n.succ+n.succ)) = 0  := by
  simp at hS1
  have hS10 := hS1 0
  change S 0 = - (S ∘ Fin.cast (n_plus_n_eq_2n n)) (Fin.natAdd n.succ 0 : Fin (n.succ+n.succ))
     at hS10
  rw [fst_eq_zero S hS2] at hS10
  linarith

lemma cond_equa (i : ℕ) (hi: i.succ < n.succ) (S : (PureU1 (2 * n.succ)).charges) (hS1 :cond₁ S)
      (hS2 :cond₂ S) :
    S ⟨i, by omega⟩ = S ⟨i.succ, by omega⟩  := by
  have hS1i : S ⟨i,  by omega⟩ = - S ⟨i + n + 1, by omega⟩ := by
    simp at hS1
    have hS11 := hS1 ⟨i,  by omega⟩
    change S ⟨i,  by omega⟩ = - S ⟨n.succ + i,  _⟩ at hS11
    rw [hS11]
    apply congrArg
    apply congrArg
    apply Fin.ext_iff.mpr
    simp
    omega
  have hS2i :  S ⟨i + n + 1, by omega⟩  = - S ⟨i.succ, by omega⟩ := by
    simp at hS2
    have hS21 := hS2.2.2 ⟨i,  by omega⟩
    change S ⟨1 + i, by omega⟩ = - S ⟨1 + (n + i), _⟩ at hS21
    have hx : S ⟨1 + i, by omega⟩ = S ⟨i.succ, by omega⟩ := by
      apply congrArg
      apply Fin.ext_iff.mpr
      simp
      omega
    rw [hx] at hS21
    rw [hS21]
    simp
    apply congrArg
    apply Fin.ext_iff.mpr
    simp
    omega
  rw [hS1i, hS2i]
  simp

lemma cond_equa₂ (i : ℕ) (hi: i < n.succ) (S : (PureU1 (2 * n.succ)).charges) (hS1 :cond₁ S)
    (hS2 :cond₂ S) : S ⟨i, by omega⟩ = 0 := by
  induction i
  exact fst_eq_zero S hS2
  rename_i i hind
  have ht := cond_equa i hi S hS1 hS2
  rw [← ht]
  refine hind ?_
  omega

lemma cond_zero (S : (PureU1 (2 * n.succ)).charges) (hS1 :cond₁ S) (hS2 : cond₂ S)
    (i : Fin (2 * n.succ)) : S i = 0 := by
  by_cases hi : i.val < n.succ
  exact cond_equa₂ i.val hi S hS1 hS2
  let i' : Fin n.succ := ⟨i.val - n.succ, by omega⟩
  have hi' : i.val = n.succ + i' := by
    simp
    refine (Nat.add_sub_of_le ?_).symm
    exact Nat.le_of_not_lt hi
  have hii : i = ⟨n.succ + i', by omega⟩ := by
    apply Fin.ext_iff.mpr
    exact hi'
  rw [hii]
  simp at hS1
  have hS11 := hS1 i'
  change S ⟨i',  by omega⟩ = - S ⟨n.succ + i',  _⟩ at hS11
  rw [cond_equa₂ i'.val (by omega) S hS1 hS2] at hS11
  exact neg_eq_zero.mp (id hS11.symm)

end intersection

def basis₃ : (Fin n.succ) ⊕ (Fin n) → (PureU1 (2 * n.succ)).charges := fun i =>
  match i with
  | .inl i => (pureU1_eq_charges (n_plus_n_eq_2n n)).toFun (basis₁ i)
  | .inr i => (pureU1_eq_charges (n_cond₂ n)).toFun (basis₂ i)

lemma basis₃_linearly_independent : LinearIndependent ℚ (@basis₃ n) := by
  apply Fintype.linearIndependent_iff.mpr
  intro g
  intro h
  intro j
  rw [Fintype.sum_sum_type] at h
  simp [basis₃] at h
  sorry

lemma card : Fintype.card ((Fin n.succ) ⊕ (Fin n)) = n.succ + n := by
  simp only [Fintype.card_sum, Fintype.card_fin]

lemma finrank_of_add :
    FiniteDimensional.finrank ℚ (PureU1 (2 * n.succ)).AnomalyFreeLinear = Fintype.card ((Fin n.succ) ⊕ (Fin n)) := by
  sorry

-- Will want to use basisOfLinearIndependentOfCardEqFinrank.

end PureU1
