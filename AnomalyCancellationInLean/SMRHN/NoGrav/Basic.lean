/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.SMRHN.Basic
import AnomalyCancellationInLean.SMRHN.Permutations
universe v u

namespace SMRHN
open SMνCharges
open SMνACCs
open BigOperators

@[simps!]
def SMNoGrav (n : ℕ) : ACCSystem where
  numberLinear := 2
  linearACCs := fun i =>
    match i with
    | 0 => @accSU2 n
    | 1 => accSU3
  numberQuadratic := 0
  quadraticACCs := by
    intro i
    exact Fin.elim0 i
  cubicACC := accCube

namespace SMNoGrav

variable {n : ℕ}

lemma SU2Sol  (S : (SMNoGrav n).AnomalyFreeLinear) : accSU2 S.val = 0 := by
  have hS := S.linearSol
  simp at hS
  exact hS 0

lemma SU3Sol  (S : (SMNoGrav n).AnomalyFreeLinear) : accSU3 S.val = 0 := by
  have hS := S.linearSol
  simp at hS
  exact hS 1

lemma cubeSol  (S : (SMNoGrav n).AnomalyFree) : accCube S.val = 0 := by
  exact S.cubicSol

/-- An element of `charges` which satisfies the linear ACCs
  gives us a element of `AnomalyFreeLinear`. -/
def chargeToLinear (S : (SMNoGrav n).charges) (hSU2 : accSU2 S = 0) (hSU3 : accSU3 S = 0) :
    (SMNoGrav n).AnomalyFreeLinear :=
  ⟨S, by
    intro i
    simp at i
    match i with
    | 0 => exact hSU2
    | 1 => exact hSU3⟩

/-- An element of `AnomalyFreeLinear` which satisfies the quadratic ACCs
  gives us a element of `AnomalyFreeQuad`. -/
def linearToQuad (S : (SMNoGrav n).AnomalyFreeLinear) : (SMNoGrav n).AnomalyFreeQuad :=
  ⟨S, by
    intro i
    exact Fin.elim0 i⟩

/-- An element of `AnomalyFreeQuad` which satisfies the quadratic ACCs
  gives us a element of `AnomalyFree`. -/
def quadToAF (S : (SMNoGrav n).AnomalyFreeQuad) (hc : accCube S.val = 0) :
    (SMNoGrav n).AnomalyFree := ⟨S, hc⟩

/-- An element of `charges` which satisfies the linear and quadratic ACCs
  gives us a element of `AnomalyFreeQuad`. -/
def chargeToQuad (S : (SMNoGrav n).charges) (hSU2 : accSU2 S = 0) (hSU3 : accSU3 S = 0) :
    (SMNoGrav n).AnomalyFreeQuad :=
  linearToQuad $ chargeToLinear S hSU2 hSU3

/-- An element of `charges` which satisfies the linear, quadratic and cubic ACCs
  gives us a element of `AnomalyFree`. -/
def chargeToAF (S : (SMNoGrav n).charges) (hSU2 : accSU2 S = 0) (hSU3 : accSU3 S = 0)
    (hc : accCube S = 0) : (SMNoGrav n).AnomalyFree :=
  quadToAF (chargeToQuad S hSU2 hSU3) hc

/-- An element of `AnomalyFreeLinear` which satisfies the  quadratic and cubic ACCs
  gives us a element of `AnomalyFree`. -/
def linearToAF (S : (SMNoGrav n).AnomalyFreeLinear)
    (hc : accCube S.val = 0) : (SMNoGrav n).AnomalyFree :=
  quadToAF (linearToQuad S) hc

def perm (n : ℕ) : ACCSystemGroupAction (SMNoGrav n) where
  group := permGroup n
  groupInst := inferInstance
  rep := repCharges
  linearInvariant := by
    intro i
    simp at i
    match i with
    | 0 => exact accSU2_invariant
    | 1 => exact accSU3_invariant
  quadInvariant := by
    intro i
    simp at i
    exact Fin.elim0 i
  cubicInvariant := accCube_invariant


end SMNoGrav

end SMRHN
