/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.SMRHN.PlusU1.Basic
import AnomalyCancellationInLean.SMRHN.FamilyMaps
universe v u

namespace SMRHN
namespace PlusU1

open SMνCharges
open SMνACCs
open BigOperators

variable {n : ℕ}

def familyUniversalLinear (n : ℕ) :
    (PlusU1 1).AnomalyFreeLinear →ₗ[ℚ] (PlusU1 n).AnomalyFreeLinear where
  toFun S := chargeToLinear (familyUniversal n S.val)
    (by rw [familyUniversal_accGrav, gravSol S, mul_zero])
    (by rw [familyUniversal_accSU2, SU2Sol S, mul_zero])
    (by rw [familyUniversal_accSU3, SU3Sol S, mul_zero])
    (by rw [familyUniversal_accYY, YYsol S, mul_zero])
  map_add' S T := by
    apply ACCSystemLinear.AnomalyFreeLinear.ext
    exact (familyUniversal n).map_add' _ _
  map_smul' a S := by
    apply ACCSystemLinear.AnomalyFreeLinear.ext
    exact (familyUniversal n).map_smul' _ _

def familyUniversalQuad (n : ℕ) :
    (PlusU1 1).AnomalyFreeQuad → (PlusU1 n).AnomalyFreeQuad := fun S =>
  chargeToQuad (familyUniversal n S.val)
    (by rw [familyUniversal_accGrav, gravSol S.1, mul_zero])
    (by rw [familyUniversal_accSU2, SU2Sol S.1, mul_zero])
    (by rw [familyUniversal_accSU3, SU3Sol S.1, mul_zero])
    (by rw [familyUniversal_accYY, YYsol S.1, mul_zero])
    (by rw [familyUniversal_accQuad, quadSol S, mul_zero])

def familyUniversalAF (n : ℕ) :
    (PlusU1 1).AnomalyFree → (PlusU1 n).AnomalyFree := fun S =>
  chargeToAF (familyUniversal n S.val)
    (by rw [familyUniversal_accGrav, gravSol S.1.1, mul_zero])
    (by rw [familyUniversal_accSU2, SU2Sol S.1.1, mul_zero])
    (by rw [familyUniversal_accSU3, SU3Sol S.1.1, mul_zero])
    (by rw [familyUniversal_accYY, YYsol S.1.1, mul_zero])
    (by rw [familyUniversal_accQuad, quadSol S.1, mul_zero])
    (by rw [familyUniversal_accCube, cubeSol S, mul_zero])

end PlusU1
end SMRHN
