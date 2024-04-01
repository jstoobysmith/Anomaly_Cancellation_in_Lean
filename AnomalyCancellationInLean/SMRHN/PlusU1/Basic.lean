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
def PlusU1 (n : ℕ) : ACCSystem where
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

namespace PlusU1


variable {n : ℕ}

lemma gravSol  (S : (PlusU1 n).AnomalyFreeLinear) : accGrav S.val = 0 := by
  have hS := S.linearSol
  simp at hS
  exact hS 0

lemma SU2Sol  (S : (PlusU1 n).AnomalyFreeLinear) : accSU2 S.val = 0 := by
  have hS := S.linearSol
  simp at hS
  exact hS 1

lemma SU3Sol  (S : (PlusU1 n).AnomalyFreeLinear) : accSU3 S.val = 0 := by
  have hS := S.linearSol
  simp at hS
  exact hS 2

lemma YYsol  (S : (PlusU1 n).AnomalyFreeLinear) : accYY S.val = 0 := by
  have hS := S.linearSol
  simp at hS
  exact hS 3

lemma quadSol  (S : (PlusU1 n).AnomalyFreeQuad) : accQuad S.val = 0 := by
  have hS := S.quadSol
  simp at hS
  exact hS 0

lemma cubeSol  (S : (PlusU1 n).AnomalyFree) : accCube S.val = 0 := by
  exact S.cubicSol

/-- An element of `charges` which satisfies the linear ACCs
  gives us a element of `AnomalyFreeLinear`. -/
def chargeToLinear (S : (PlusU1 n).charges) (hGrav : accGrav S = 0)
    (hSU2 : accSU2 S = 0) (hSU3 : accSU3 S = 0) (hYY : accYY S = 0) :
    (PlusU1 n).AnomalyFreeLinear :=
  ⟨S, by
    intro i
    simp at i
    match i with
    | 0 => exact hGrav
    | 1 => exact hSU2
    | 2 => exact hSU3
    | 3 => exact hYY⟩

/-- An element of `AnomalyFreeLinear` which satisfies the quadratic ACCs
  gives us a element of `AnomalyFreeQuad`. -/
def linearToQuad (S : (PlusU1 n).AnomalyFreeLinear) (hQ : accQuad S.val = 0) :
    (PlusU1 n).AnomalyFreeQuad :=
  ⟨S, by
    intro i
    simp at i
    match i with
    | 0 => exact hQ⟩

/-- An element of `AnomalyFreeQuad` which satisfies the quadratic ACCs
  gives us a element of `AnomalyFree`. -/
def quadToAF (S : (PlusU1 n).AnomalyFreeQuad) (hc : accCube S.val = 0) :
    (PlusU1 n).AnomalyFree := ⟨S, hc⟩

/-- An element of `charges` which satisfies the linear and quadratic ACCs
  gives us a element of `AnomalyFreeQuad`. -/
def chargeToQuad (S : (PlusU1 n).charges) (hGrav : accGrav S = 0)
    (hSU2 : accSU2 S = 0) (hSU3 : accSU3 S = 0) (hYY : accYY S = 0) (hQ : accQuad S = 0) :
    (PlusU1 n).AnomalyFreeQuad :=
  linearToQuad (chargeToLinear S hGrav hSU2 hSU3 hYY) hQ

/-- An element of `charges` which satisfies the linear, quadratic and cubic ACCs
  gives us a element of `AnomalyFree`. -/
def chargeToAF (S : (PlusU1 n).charges) (hGrav : accGrav S = 0) (hSU2 : accSU2 S = 0)
    (hSU3 : accSU3 S = 0) (hYY : accYY S = 0) (hQ : accQuad S = 0) (hc : accCube S = 0) :
    (PlusU1 n).AnomalyFree :=
  quadToAF (chargeToQuad S hGrav hSU2 hSU3 hYY hQ) hc

/-- An element of `AnomalyFreeLinear` which satisfies the  quadratic and cubic ACCs
  gives us a element of `AnomalyFree`. -/
def linearToAF (S : (PlusU1 n).AnomalyFreeLinear) (hQ : accQuad S.val = 0)
    (hc : accCube S.val = 0) : (PlusU1 n).AnomalyFree :=
  quadToAF (linearToQuad S hQ) hc

def perm (n : ℕ) : ACCSystemGroupAction (PlusU1 n) where
  group := permGroup n
  groupInst := inferInstance
  rep := repCharges
  linearInvariant := by
    intro i
    simp at i
    match i with
    | 0 => exact accGrav_invariant
    | 1 => exact accSU2_invariant
    | 2 => exact accSU3_invariant
    | 3 => exact accYY_invariant
  quadInvariant := by
    intro i
    simp at i
    match i with
    | 0 => exact accQuad_invariant
  cubicInvariant := accCube_invariant

end PlusU1

end SMRHN
