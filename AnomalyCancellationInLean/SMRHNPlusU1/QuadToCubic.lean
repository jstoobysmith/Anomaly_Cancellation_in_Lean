/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.SMRHNPlusU1.BMinusL


universe v u

namespace SMRHNPlusU1
open SMRHNPlusU1Charges
open SMRHNPlusU1ACCs
open BigOperators

namespace QuadToCubic

@[simp]
def α₁ {n : ℕ} (S : (SMRHNPlusU1 n).AnomalyFreeQuad) : ℚ :=
  - 3 * accCubeTriLinSymm.toFun (S.val, S.val, (BMinusLNFamily n).val)

@[simp]
def α₂ {n : ℕ} (S : (SMRHNPlusU1 n).AnomalyFreeQuad) : ℚ :=
  (accCube.toFun S.val)


@[simps!]
def generic {n : ℕ} (S : (SMRHNPlusU1 n).AnomalyFreeQuad) : (SMRHNPlusU1 n).AnomalyFree :=
  ⟨anomalyFreeQuadPlusBMinusL (α₂ S) ((α₁ S) • S),
  by
   simp only [anomalyFreeQuadPlusBMinusL]
   erw [TriLinearSymm.toHomogeneousCubic_add]
   erw [HomogeneousCubic.map_smul']
   erw [HomogeneousCubic.map_smul']
   erw [TriLinear.map_smul₁, TriLinear.map_smul₁]
   erw [TriLinear.map_smul₂, TriLinear.map_smul₂]
   erw [TriLinear.map_smul₃, TriLinear.map_smul₃]
   erw [(BMinusLNFamily n).cubicSol]
   rw [accCubeTriLinear_BMinusL₂_AnomalyFreeLinear]
   rw [α₁]
   ring_nf
   simp
  ⟩

lemma generic_on_AnomalyFree (S : (SMRHNPlusU1 n).AnomalyFree) :
    generic S.1 = (α₁ S.1) • S := by
  rw [generic]
  apply ACCSystem.AnomalyFree.ext
  simp only
  rw [α₂]
  erw [S.cubicSol]
  rw [anomalyFreeQuadPlusBMinusL_zero]
  rfl

def special (S : (SMRHNPlusU1 n).AnomalyFreeQuad)
    (h1 : α₁ S = 0) (h2 : α₂ S = 0) (a b : ℚ) : (SMRHNPlusU1 n).AnomalyFree :=
  ⟨anomalyFreeQuadPlusBMinusL a (b • S), by
    simp only [anomalyFreeQuadPlusBMinusL]
    erw [TriLinearSymm.toHomogeneousCubic_add]
    erw [HomogeneousCubic.map_smul']
    erw [HomogeneousCubic.map_smul']
    erw [TriLinear.map_smul₁, TriLinear.map_smul₁]
    erw [TriLinear.map_smul₂, TriLinear.map_smul₂]
    erw [TriLinear.map_smul₃, TriLinear.map_smul₃]
    rw [accCubeTriLinear_BMinusL₂_AnomalyFreeLinear]
    erw [(BMinusLNFamily n).cubicSol]
    simp_all
  ⟩


end QuadToCubic

open QuadToCubic

@[simp]
def quadToCube (n : ℕ) : (SMRHNPlusU1 n).AnomalyFreeQuad × ℚ × ℚ → (SMRHNPlusU1 n).AnomalyFree :=
  fun S =>
    if h : α₁ S.1 = 0 ∧ α₂ S.1 = 0 then
      special S.1 h.left h.right S.2.1 S.2.2
    else
      S.2.1 • (generic S.1)

theorem quadToCube_surjective (n : ℕ) : Function.Surjective (quadToCube n) := by
  intro S
  by_cases hS :  α₁ S.1 = 0 ∧ α₂ S.1 = 0
  · use ⟨S.1, ⟨0, 1⟩⟩
    rw [quadToCube]
    rw [dif_pos hS]
    rw [special]
    apply ACCSystem.AnomalyFree.ext
    simp [anomalyFreeQuadPlusBMinusL]
  · use ⟨S.1, ⟨1/(α₁ S.1), 0⟩⟩
    rw [quadToCube]
    rw [dif_neg hS]
    rw [generic_on_AnomalyFree]
    rw [← (SMRHNPlusU1 n).AnomalyFreeMulAction.mul_smul]
    rw [div_mul]
    rw [one_div_div]
    rw [div_self, (SMRHNPlusU1 n).AnomalyFreeMulAction.one_smul]
    erw [α₂, S.cubicSol] at hS
    simp_all only [α₁, SMRHNPlusU1Charges_charges, BMinusLNFamily_val, accCubeTriLinSymm_toFun,
      neg_mul, neg_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, false_or, and_true, ne_eq, or_self,
      not_false_eq_true]

end SMRHNPlusU1
