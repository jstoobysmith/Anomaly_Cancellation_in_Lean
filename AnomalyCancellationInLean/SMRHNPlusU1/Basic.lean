/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic.Ring
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
import AnomalyCancellationInLean.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin
/-!
# Anomaly cancellation conditions for n families with RHN.

-/

universe v u
open Nat
open BigOperators

@[simps!]
def SMRHNPlusU1Charges (n : ℕ) : ACCSystemCharges := ACCSystemChargesMk (6 * n)

@[simps!]
def SMRHNPlusU1Species (n : ℕ) : ACCSystemCharges := ACCSystemChargesMk n

namespace SMRHNPlusU1Charges

@[simps!]
def toSpeciesMaps {n : ℕ} : (SMRHNPlusU1Charges n).charges ≃ (Fin 6 → Fin n → ℚ) :=
   ((Equiv.curry _ _ _).symm.trans
    ((@finProdFinEquiv 6 n).arrowCongr (Equiv.refl ℚ))).symm

@[simp]
def mkFromSpecies {n : ℕ} (SQ SU SD SL SE SN : Fin n → ℚ) :
  (SMRHNPlusU1Charges n).charges := toSpeciesMaps.invFun ( fun i =>
    match i with
    | 0 => SQ
    | 1 => SU
    | 2 => SD
    | 3 => SL
    | 4 => SE
    | 5 => SN
  )

@[simps!]
def Q {n : ℕ} : (SMRHNPlusU1Charges n).charges →ₗ[ℚ] (SMRHNPlusU1Species n).charges where
  toFun S := toSpeciesMaps S 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simps!]
def U {n : ℕ} : (SMRHNPlusU1Charges n).charges →ₗ[ℚ] (SMRHNPlusU1Species n).charges where
  toFun S := toSpeciesMaps S 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simps!]
def D {n : ℕ} : (SMRHNPlusU1Charges n).charges →ₗ[ℚ] (SMRHNPlusU1Species n).charges where
  toFun S := toSpeciesMaps S 2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simps!]
def L {n : ℕ} : (SMRHNPlusU1Charges n).charges →ₗ[ℚ] (SMRHNPlusU1Species n).charges where
  toFun S := toSpeciesMaps S 3
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simps!]
def E {n : ℕ} : (SMRHNPlusU1Charges n).charges →ₗ[ℚ] (SMRHNPlusU1Species n).charges where
  toFun S := toSpeciesMaps S 4
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simps!]
def N {n : ℕ} : (SMRHNPlusU1Charges n).charges →ₗ[ℚ] (SMRHNPlusU1Species n).charges where
  toFun S := toSpeciesMaps S 5
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma ext {n : ℕ} {S T : (SMRHNPlusU1Charges n).charges}
    (hQ : Q.toFun S = Q.toFun T) (hU : U.toFun S = U.toFun T) (hD : D.toFun S = D.toFun T)
    (hL : L.toFun S = L.toFun T) (hE : E.toFun S = E.toFun T) (hN : N.toFun S = N.toFun T) : S = T := by
  apply  (@SMRHNPlusU1Charges.toSpeciesMaps n).apply_eq_iff_eq.mp
  funext i
  match i with
  | 0 => exact hQ
  | 1 => exact hU
  | 2 => exact hD
  | 3 => exact hL
  | 4 => exact hE
  | 5 => exact hN

lemma mkFromSpecies_Q {n : ℕ} (SQ SU SD SL SE SN : Fin n → ℚ) :
    Q.toFun (mkFromSpecies SQ SU SD SL SE SN) = SQ := by
  change toSpeciesMaps (toSpeciesMaps.invFun _) _  = _
  simp

lemma mkFromSpecies_U {n : ℕ} (SQ SU SD SL SE SN : Fin n → ℚ) :
    U.toFun (mkFromSpecies SQ SU SD SL SE SN) = SU := by
  change toSpeciesMaps (toSpeciesMaps.invFun _) _  = _
  simp

lemma mkFromSpecies_D {n : ℕ} (SQ SU SD SL SE SN : Fin n → ℚ) :
    D.toFun (mkFromSpecies SQ SU SD SL SE SN) = SD := by
  change toSpeciesMaps (toSpeciesMaps.invFun _) _  = _
  simp

lemma mkFromSpecies_L {n : ℕ} (SQ SU SD SL SE SN : Fin n → ℚ) :
    L.toFun (mkFromSpecies SQ SU SD SL SE SN) = SL := by
  change toSpeciesMaps (toSpeciesMaps.invFun _) _  = _
  simp

lemma mkFromSpecies_E {n : ℕ} (SQ SU SD SL SE SN : Fin n → ℚ) :
    E.toFun (mkFromSpecies SQ SU SD SL SE SN) = SE := by
  change toSpeciesMaps (toSpeciesMaps.invFun _) _  = _
  simp

lemma mkFromSpecies_N {n : ℕ} (SQ SU SD SL SE SN : Fin n → ℚ) :
    N.toFun (mkFromSpecies SQ SU SD SL SE SN) = SN := by
  change toSpeciesMaps (toSpeciesMaps.invFun _) _  = _
  simp


end SMRHNPlusU1Charges


namespace SMRHNPlusU1ACCs

open SMRHNPlusU1Charges


@[simp]
def accGrav {n : ℕ} : (SMRHNPlusU1Charges n).charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (6 * (Q.toFun S) i + 3 * (U.toFun S) i + 3 * (D.toFun S) i
    + 2 * (L.toFun S) i + (E.toFun S) i + (N.toFun S) i)
  map_add' S T := by
    simp [toSpeciesMaps]
    simp only [Rat.mul_add]
    repeat erw [Finset.sum_add_distrib]
    ring
  map_smul' a S := by
    simp [toSpeciesMaps, HSMul.hSMul, SMul.smul]
    erw [Q.map_smul, U.map_smul, D.map_smul, L.map_smul, E.map_smul, N.map_smul]
    simp [toSpeciesMaps, HSMul.hSMul, SMul.smul]
    repeat erw [Finset.sum_add_distrib]
    repeat erw [← Finset.mul_sum]
    rw [show Rat.cast a = a from rfl]
    ring

lemma accGrav_eq_of_sum_eq {n : ℕ} {S T : (SMRHNPlusU1Charges n).charges}
    (hQ : ∑ i, (Q.toFun S) i = ∑ i, (Q.toFun T) i)
    (hU : ∑ i, (U.toFun S) i = ∑ i, (U.toFun T) i)
    (hD : ∑ i, (D.toFun S) i = ∑ i, (D.toFun T) i)
    (hL : ∑ i, (L.toFun S) i = ∑ i, (L.toFun T) i)
    (hE : ∑ i, (E.toFun S) i = ∑ i, (E.toFun T) i)
    (hN : ∑ i, (N.toFun S) i = ∑ i, (N.toFun T) i) :
    accGrav S = accGrav T := by
  simp
  repeat erw [Finset.sum_add_distrib]
  repeat erw [← Finset.mul_sum]
  erw [hQ, hU, hD, hL, hE, hN]
  rfl


/-- The anomaly cancelation condition for SU(2) anomaly. -/
@[simp]
def accSU2 {n : ℕ} : (SMRHNPlusU1Charges n).charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (3 * (Q.toFun S) i + (L.toFun S) i)
  map_add' S T := by
    simp [toSpeciesMaps]
    simp only [Rat.mul_add]
    repeat erw [Finset.sum_add_distrib]
    ring
  map_smul' a S := by
    simp only
    simp [toSpeciesMaps, HSMul.hSMul, SMul.smul]
    erw [Q.map_smul, L.map_smul]
    simp [toSpeciesMaps, HSMul.hSMul, SMul.smul]
    repeat erw [Finset.sum_add_distrib]
    repeat erw [← Finset.mul_sum]
    rw [show Rat.cast a = a from rfl]
    ring

lemma accSU2_eq_of_sum_eq {n : ℕ} {S T : (SMRHNPlusU1Charges n).charges}
    (hQ : ∑ i, (Q.toFun S) i = ∑ i, (Q.toFun T) i)
    (hL : ∑ i, (L.toFun S) i = ∑ i, (L.toFun T) i) :
    accSU2 S = accSU2 T := by
  simp
  repeat erw [Finset.sum_add_distrib]
  repeat erw [← Finset.mul_sum]
  erw [hQ, hL]
  rfl

/-- The anomaly cancelation condition for SU(2) anomaly. -/
@[simp]
def accSU3 {n : ℕ} : (SMRHNPlusU1Charges n).charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, (2 * (Q.toFun S i) + (U.toFun S i) + (D.toFun S i))
  map_add' S T := by
    simp [toSpeciesMaps]
    simp only [Rat.mul_add]
    repeat erw [Finset.sum_add_distrib]
    ring
  map_smul' a S := by
    simp [toSpeciesMaps, HSMul.hSMul, SMul.smul]
    erw [Q.map_smul, U.map_smul, D.map_smul]
    simp [toSpeciesMaps, HSMul.hSMul, SMul.smul]
    repeat erw [Finset.sum_add_distrib]
    repeat erw [← Finset.mul_sum]
    rw [show Rat.cast a = a from rfl]
    ring

lemma accSU3_eq_of_sum_eq {n : ℕ} {S T : (SMRHNPlusU1Charges n).charges}
    (hQ : ∑ i, (Q.toFun S) i = ∑ i, (Q.toFun T) i)
    (hU : ∑ i, (U.toFun S) i = ∑ i, (U.toFun T) i)
    (hD : ∑ i, (D.toFun S) i = ∑ i, (D.toFun T) i) :
    accSU3 S = accSU3 T := by
  simp
  repeat erw [Finset.sum_add_distrib]
  repeat erw [← Finset.mul_sum]
  erw [hQ, hU, hD]
  rfl

/-- The anomaly cancelation condition for Y² anomaly. -/
@[simp]
def accYY {n : ℕ} : (SMRHNPlusU1Charges n).charges →ₗ[ℚ] ℚ where
  toFun S := ∑ i, ((Q.toFun S) i + 8 * (U.toFun S) i + 2 * (D.toFun S) i + 3 * (L.toFun S) i
    + 6 * (E.toFun S) i)
  map_add' S T := by
    simp [toSpeciesMaps]
    simp only [Rat.mul_add]
    repeat rw [Finset.sum_add_distrib]
    ring
  map_smul' a S := by
    simp [toSpeciesMaps, HSMul.hSMul, SMul.smul]
    erw [Q.map_smul, U.map_smul, D.map_smul, L.map_smul, E.map_smul]
    simp [toSpeciesMaps, HSMul.hSMul, SMul.smul]
    repeat erw [Finset.sum_add_distrib]
    repeat erw [← Finset.mul_sum]
    rw [show Rat.cast a = a from rfl]
    ring

lemma accYY_eq_of_sum_eq {n : ℕ} {S T : (SMRHNPlusU1Charges n).charges}
    (hQ : ∑ i, (Q.toFun S) i = ∑ i, (Q.toFun T) i)
    (hU : ∑ i, (U.toFun S) i = ∑ i, (U.toFun T) i)
    (hD : ∑ i, (D.toFun S) i = ∑ i, (D.toFun T) i)
    (hL : ∑ i, (L.toFun S) i = ∑ i, (L.toFun T) i)
    (hE : ∑ i, (E.toFun S) i = ∑ i, (E.toFun T) i) :
    accYY S = accYY T := by
  simp
  repeat erw [Finset.sum_add_distrib]
  repeat erw [← Finset.mul_sum]
  erw [hQ, hU, hD, hL, hE]
  rfl

@[simps!]
def accQuadBiLinear {n : ℕ} : BiLinearSymm (SMRHNPlusU1Charges n).charges where
  toFun S := ∑ i, ((Q.toFun S.1 i) *  (Q.toFun S.2 i) +
    (- 2 * ((U.toFun S.1 i) *  (U.toFun S.2 i))) +
    (((D.toFun S.1 i) *  (D.toFun S.2 i)))
    + (- ((L.toFun S.1 i) * (L.toFun S.2 i)))  +
    (((E.toFun S.1 i) * (E.toFun S.2 i))))
  map_smul₁ a S T := by
    simp
    rw [Finset.mul_sum]
    apply Fintype.sum_congr
    intro i
    erw [Q.map_smul, U.map_smul, D.map_smul, L.map_smul, E.map_smul]
    simp [toSpeciesMaps, HSMul.hSMul, SMul.smul]
    ring
  map_smul₂ a S T := by
    simp
    rw [Finset.mul_sum]
    apply Fintype.sum_congr
    intro i
    erw [Q.map_smul, U.map_smul, D.map_smul, L.map_smul, E.map_smul]
    simp [toSpeciesMaps, HSMul.hSMul, SMul.smul]
    ring
  map_add₁ S T L := by
    simp
    rw [← Finset.sum_add_distrib]
    apply Fintype.sum_congr
    intro i
    ring
  map_add₂ S T L := by
    simp
    rw [← Finset.sum_add_distrib]
    apply Fintype.sum_congr
    intro i
    ring
  swap S L := by
    simp
    apply Fintype.sum_congr
    intro i
    ring
/-- The anomaly cancelation condition for Y anomaly. -/
@[simp]
def accQuad {n : ℕ} : HomogeneousQuadratic (SMRHNPlusU1Charges n).charges :=
   (@accQuadBiLinear n).toHomogeneousQuad

lemma accQuad_eq_of_sum_sq_eq {n : ℕ} {S T : (SMRHNPlusU1Charges n).charges}
    (hQ : ∑ i, ((fun a => a^2) ∘ (Q.toFun S)) i = ∑ i, ((fun a => a^2) ∘ (Q.toFun T)) i)
    (hU : ∑ i, ((fun a => a^2) ∘ (U.toFun S)) i = ∑ i, ((fun a => a^2) ∘ (U.toFun T)) i)
    (hD : ∑ i, ((fun a => a^2) ∘ (D.toFun S)) i = ∑ i, ((fun a => a^2) ∘ (D.toFun T)) i)
    (hL : ∑ i, ((fun a => a^2) ∘ (L.toFun S)) i = ∑ i, ((fun a => a^2) ∘ (L.toFun T)) i)
    (hE : ∑ i, ((fun a => a^2) ∘ (E.toFun S)) i = ∑ i, ((fun a => a^2) ∘ (E.toFun T)) i) :
    accQuad.toFun S = accQuad.toFun T := by
  simp
  repeat erw [Finset.sum_add_distrib]
  repeat erw [Finset.sum_neg_distrib]
  repeat erw [← Finset.mul_sum]
  ring_nf
  erw [hQ, hU, hD, hL, hE]
  rfl

@[simp]
def accCubeTriLinToFun {n : ℕ}
    (S : (SMRHNPlusU1Charges n).charges × (SMRHNPlusU1Charges n).charges ×
    (SMRHNPlusU1Charges n).charges) : ℚ :=
   ∑ i, (6 * ((Q.toFun S.1 i) * (Q.toFun S.2.1 i) * (Q.toFun S.2.2 i))
    + 3 * ((U.toFun S.1 i) * (U.toFun S.2.1 i) * (U.toFun S.2.2 i))
    + 3 * ((D.toFun S.1 i) * (D.toFun S.2.1 i) * (D.toFun S.2.2 i))
    + 2 * ((L.toFun S.1 i) * (L.toFun S.2.1 i) * (L.toFun S.2.2 i))
    +  ((E.toFun S.1 i) * (E.toFun S.2.1 i) * (E.toFun S.2.2 i))
    +  ((N.toFun S.1 i) * (N.toFun S.2.1 i) * (N.toFun S.2.2 i)))

lemma accCubeTriLinToFun_map_smul₁ {n : ℕ} (a : ℚ)  (S T R : (SMRHNPlusU1Charges n).charges) :
    accCubeTriLinToFun (a • S, T, R) = a * accCubeTriLinToFun (S, T, R) := by
  simp only [accCubeTriLinToFun, SMRHNPlusU1Charges_charges, SMRHNPlusU1Species_charges,
    AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro i
  erw [Q.map_smul, U.map_smul, D.map_smul, L.map_smul, E.map_smul, N.map_smul]
  simp [toSpeciesMaps, HSMul.hSMul, SMul.smul]
  ring

lemma accCubeTriLinToFun_map_smul₂ {n : ℕ} (a : ℚ)  (S T R : (SMRHNPlusU1Charges n).charges) :
    accCubeTriLinToFun (S, a • T, R) = a * accCubeTriLinToFun (S, T, R) := by
  simp only [accCubeTriLinToFun, SMRHNPlusU1Charges_charges, SMRHNPlusU1Species_charges,
    AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro i
  erw [Q.map_smul, U.map_smul, D.map_smul, L.map_smul, E.map_smul, N.map_smul]
  simp [toSpeciesMaps, HSMul.hSMul, SMul.smul]
  ring

lemma accCubeTriLinToFun_map_smul₃ {n : ℕ} (a : ℚ)  (S T R : (SMRHNPlusU1Charges n).charges) :
    accCubeTriLinToFun (S, T, a •  R) = a * accCubeTriLinToFun (S, T, R) := by
  simp only [accCubeTriLinToFun, SMRHNPlusU1Charges_charges, SMRHNPlusU1Species_charges,
    AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
  rw [Finset.mul_sum]
  apply Fintype.sum_congr
  intro i
  erw [Q.map_smul, U.map_smul, D.map_smul, L.map_smul, E.map_smul, N.map_smul]
  simp [toSpeciesMaps, HSMul.hSMul, SMul.smul]
  ring

@[simps!]
def accCubeTriLinSymm {n : ℕ} : TriLinearSymm (SMRHNPlusU1Charges n).charges where
  toFun S := accCubeTriLinToFun S
  map_smul₁ := accCubeTriLinToFun_map_smul₁
  map_smul₂ := accCubeTriLinToFun_map_smul₂
  map_smul₃ := accCubeTriLinToFun_map_smul₃
  map_add₁ S L T R := by
    simp
    rw [← Finset.sum_add_distrib]
    apply Fintype.sum_congr
    intro i
    ring
  map_add₂ S L T R := by
    simp
    rw [← Finset.sum_add_distrib]
    apply Fintype.sum_congr
    intro i
    ring
  map_add₃ S L T R := by
    simp
    rw [← Finset.sum_add_distrib]
    apply Fintype.sum_congr
    intro i
    ring
  swap₁ S L T := by
    simp
    apply Fintype.sum_congr
    intro i
    ring
  swap₂ S L T := by
    simp
    apply Fintype.sum_congr
    intro i
    ring

@[simp]
def accCube {n : ℕ} : HomogeneousCubic (SMRHNPlusU1Charges n).charges :=
  (@accCubeTriLinSymm n).toHomogeneousCubic


lemma accCube_eq_of_sum_cube_eq {n : ℕ} {S T : (SMRHNPlusU1Charges n).charges}
    (hQ : ∑ i, ((fun a => a^3) ∘ (Q.toFun S)) i = ∑ i, ((fun a => a^3) ∘ (Q.toFun T)) i)
    (hU : ∑ i, ((fun a => a^3) ∘ (U.toFun S)) i = ∑ i, ((fun a => a^3) ∘ (U.toFun T)) i)
    (hD : ∑ i, ((fun a => a^3) ∘ (D.toFun S)) i = ∑ i, ((fun a => a^3) ∘ (D.toFun T)) i)
    (hL : ∑ i, ((fun a => a^3) ∘ (L.toFun S)) i = ∑ i, ((fun a => a^3) ∘ (L.toFun T)) i)
    (hE : ∑ i, ((fun a => a^3) ∘ (E.toFun S)) i = ∑ i, ((fun a => a^3) ∘ (E.toFun T)) i)
    (hN : ∑ i, ((fun a => a^3) ∘ (N.toFun S)) i = ∑ i, ((fun a => a^3) ∘ (N.toFun T)) i) :
    accCube.toFun S = accCube.toFun T := by
  simp
  repeat erw [Finset.sum_add_distrib]
  repeat erw [Finset.sum_neg_distrib]
  repeat erw [← Finset.mul_sum]
  ring_nf
  erw [hQ, hU, hD, hL, hE, hN]
  rfl


end SMRHNPlusU1ACCs

open SMRHNPlusU1ACCs

@[simps!]
def SMRHNPlusU1 (n : ℕ) : ACCSystem where
  numberLinear := 4
  linearACCs := fun i =>
    match i with
    | 0 => @accGrav n
    | 1 => accSU2
    | 2 => accSU3
    | 3 => accYY
  numberQuadratic := 1
  quadraticACCs := fun i =>
    match i with
    | 0 => accQuad
  cubicACC := accCube
