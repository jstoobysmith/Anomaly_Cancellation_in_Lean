/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.SMRHN.Ordinary.Basic
import AnomalyCancellationInLean.SMRHN.FamilyMaps
universe v u

namespace SMRHN
namespace SM

open SMνCharges
open SMνACCs
open BigOperators

variable {n : ℕ}

def familyUniversalLinear (n : ℕ) :
    (SM 1).LinSols →ₗ[ℚ] (SM n).LinSols where
  toFun S := chargeToLinear (familyUniversal n S.val)
    (by rw [familyUniversal_accGrav, gravSol S, mul_zero])
    (by rw [familyUniversal_accSU2, SU2Sol S, mul_zero])
    (by rw [familyUniversal_accSU3, SU3Sol S, mul_zero])
  map_add' S T := by
    apply ACCSystemLinear.LinSols.ext
    exact (familyUniversal n).map_add' _ _
  map_smul' a S := by
    apply ACCSystemLinear.LinSols.ext
    exact (familyUniversal n).map_smul' _ _

def familyUniversalQuad (n : ℕ) :
    (SM 1).QuadSols → (SM n).QuadSols := fun S =>
  chargeToQuad (familyUniversal n S.val)
    (by rw [familyUniversal_accGrav, gravSol S.1, mul_zero])
    (by rw [familyUniversal_accSU2, SU2Sol S.1, mul_zero])
    (by rw [familyUniversal_accSU3, SU3Sol S.1, mul_zero])

def familyUniversalAF (n : ℕ) :
    (SM 1).Sols → (SM n).Sols := fun S =>
  chargeToAF (familyUniversal n S.val)
    (by rw [familyUniversal_accGrav, gravSol S.1.1, mul_zero])
    (by rw [familyUniversal_accSU2, SU2Sol S.1.1, mul_zero])
    (by rw [familyUniversal_accSU3, SU3Sol S.1.1, mul_zero])
    (by rw [familyUniversal_accCube, cubeSol S, mul_zero])

end SM
end SMRHN
