/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.LinearMaps
import Mathlib.Tactic.Polyrith
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.NumberTheory.FLT.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap.Basic
/-!
# Basic set up for anomaly cancellation conditions

This file defines the basic structures for the anomaly cancellation conditions.

It defines a module structure on the charges, and the solutions to the linear ACCs.

## TODO

In the future information about the fermionic representations, and the gauge algebra
should lead to an ACCSystem.

-/

/-- A system of charges, specified by the number of charges. -/
structure ACCSystemCharges where
  numberCharges : ℕ

/--
  Creates an `ACCSystemCharges` object with the specified number of charges.
-/
def ACCSystemChargesMk (n : ℕ) : ACCSystemCharges where
  numberCharges := n

namespace ACCSystemCharges

/-- The charges as functions from `Fin χ.numberCharges → ℚ`. -/
def charges (χ : ACCSystemCharges) : Type := Fin χ.numberCharges → ℚ

@[simps!]
instance chargesAddCommMonoid (χ : ACCSystemCharges) : AddCommMonoid χ.charges :=
  Pi.addCommMonoid

@[simps!]
instance chargesModule (χ : ACCSystemCharges) : Module ℚ χ.charges :=
  Pi.module _ _ _

instance ChargesAddCommGroup (χ : ACCSystemCharges) :
    AddCommGroup χ.charges :=
  Module.addCommMonoidToAddCommGroup ℚ

end ACCSystemCharges

structure ACCSystemLinear extends ACCSystemCharges where
  numberLinear : ℕ
  linearACCs :  Fin numberLinear → (toACCSystemCharges.charges →ₗ[ℚ] ℚ)

namespace ACCSystemLinear

structure LinSols (χ : ACCSystemLinear) where
  val : χ.1.charges
  linearSol : ∀ i : Fin χ.numberLinear, χ.linearACCs i val = 0

@[ext]
lemma LinSols.ext {χ : ACCSystemLinear} {S T : χ.LinSols} (h : S.val = T.val) :
    S = T := by
  cases' S
  simp_all only

@[simps!]
instance linSolsAddCommMonoid (χ : ACCSystemLinear) :
    AddCommMonoid χ.LinSols where
  add S T := ⟨S.val + T.val, by
    intro i
    rw [(χ.linearACCs i).map_add, S.linearSol i, T.linearSol i]
    rfl⟩
  add_comm S T := by
    apply LinSols.ext
    exact χ.chargesAddCommMonoid.add_comm _ _
  add_assoc S T L := by
    apply LinSols.ext
    exact χ.chargesAddCommMonoid.add_assoc _ _ _
  zero := ⟨χ.chargesAddCommMonoid.zero, by
    intro i
    erw [(χ.linearACCs i).map_zero]⟩
  zero_add S := by
    apply LinSols.ext
    exact χ.chargesAddCommMonoid.zero_add _
  add_zero S := by
    apply LinSols.ext
    exact χ.chargesAddCommMonoid.add_zero _
  nsmul n S := ⟨n  • S.val, by
    intro i
    rw [nsmul_eq_smul_cast ℚ]
    erw [(χ.linearACCs i).map_smul, S.linearSol i]
    simp⟩
  nsmul_zero n := by
    rfl
  nsmul_succ n S := by
    apply LinSols.ext
    exact χ.chargesAddCommMonoid.nsmul_succ _ _

@[simps!]
instance linSolsModule  (χ : ACCSystemLinear) : Module ℚ χ.LinSols where
  smul a S := ⟨a • S.val, by
    intro i
    rw [(χ.linearACCs i).map_smul, S.linearSol i]
    simp⟩
  one_smul one_smul := by
    apply LinSols.ext
    exact χ.chargesModule.one_smul _
  mul_smul a b S := by
    apply LinSols.ext
    exact χ.chargesModule.mul_smul _ _ _
  smul_zero a := by
    apply LinSols.ext
    exact χ.chargesModule.smul_zero _
  zero_smul S := by
    apply LinSols.ext
    exact χ.chargesModule.zero_smul _
  smul_add a S T := by
    apply LinSols.ext
    exact χ.chargesModule.smul_add _ _ _
  add_smul a b T:= by
    apply LinSols.ext
    exact χ.chargesModule.add_smul _ _ _

instance linSolsAddCommGroup (χ : ACCSystemLinear) :
    AddCommGroup χ.LinSols :=
  Module.addCommMonoidToAddCommGroup ℚ

/-- The linear map reperesenting the
 inclusion of charges satisfying the linear anomaly free equations into all charges. -/
def linSolsIncl (χ : ACCSystemLinear) : χ.LinSols →ₗ[ℚ] χ.charges where
  toFun S := S.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end ACCSystemLinear

structure ACCSystemQuad extends ACCSystemLinear where
  numberQuadratic : ℕ
  quadraticACCs : Fin numberQuadratic → HomogeneousQuadratic toACCSystemCharges.charges

namespace ACCSystemQuad

structure QuadSols (χ : ACCSystemQuad) extends χ.LinSols where
  quadSol : ∀ i : Fin χ.numberQuadratic, (χ.quadraticACCs i) val = 0

@[ext]
lemma QuadSols.ext {χ : ACCSystemQuad} {S T : χ.QuadSols} (h : S.val = T.val) :
    S = T := by
  have h  := ACCSystemLinear.LinSols.ext h
  cases' S
  simp_all only

/-- The scalar multiple of any solution to the linear + quadratic equations is still a solution. -/
instance quadSolsMulAction (χ : ACCSystemQuad) : MulAction ℚ χ.QuadSols where
  smul a S :=  ⟨a • S.toLinSols , by
    intro i
    erw [(χ.quadraticACCs i).map_smul]
    rw [S.quadSol i]
    simp
    ⟩
  mul_smul a b S := by
    apply QuadSols.ext
    exact mul_smul _ _ _
  one_smul S := by
    apply QuadSols.ext
    exact one_smul _ _

def quadSolsInclLinSols (χ : ACCSystemQuad) :
    MulActionHom ℚ χ.QuadSols χ.LinSols  where
  toFun  := QuadSols.toLinSols
  map_smul' _ _ := rfl


def linSolsInclQuadSolsZero (χ : ACCSystemQuad) (h : χ.numberQuadratic = 0) :
    MulActionHom ℚ χ.LinSols χ.QuadSols where
  toFun S := ⟨S, by intro i; rw [h] at i; exact Fin.elim0 i⟩
  map_smul' _ _ := rfl

def quadSolsIncl (χ : ACCSystemQuad) :
    MulActionHom ℚ χ.QuadSols χ.charges :=
  MulActionHom.comp χ.linSolsIncl  χ.quadSolsInclLinSols

end ACCSystemQuad

structure ACCSystem extends ACCSystemQuad where
  cubicACC : HomogeneousCubic toACCSystemCharges.charges

namespace ACCSystem

structure Sols (χ : ACCSystem) extends χ.QuadSols where
  cubicSol : χ.cubicACC val = 0

lemma Sols.ext {χ : ACCSystem} {S T : χ.Sols} (h : S.val = T.val) :
    S = T := by
  have h  := ACCSystemQuad.QuadSols.ext h
  cases' S
  simp_all only

/-- The scalar multiple of any solution to the linear + quadratic equations is still a solution. -/
instance solsMulAction (χ : ACCSystem) : MulAction ℚ χ.Sols where
  smul a S :=  ⟨a • S.toQuadSols , by
    erw [(χ.cubicACC).map_smul]
    rw [S.cubicSol]
    simp⟩
  mul_smul a b S := by
    apply Sols.ext
    exact mul_smul _ _ _
  one_smul S := by
    apply Sols.ext
    exact one_smul _ _

/-- The inclusion of the anomaly free solution into solutions of the quadratic and
linear equations -/
def solsInclQuadSols (χ : ACCSystem) :
    MulActionHom ℚ χ.Sols χ.QuadSols  where
  toFun  := Sols.toQuadSols
  map_smul' _ _ := rfl

/-- The inclusion of anomaly free solutions into all solutions of the linear equations. -/
def solsInclLinSols (χ : ACCSystem) : MulActionHom ℚ χ.Sols χ.LinSols :=
  MulActionHom.comp χ.quadSolsInclLinSols χ.solsInclQuadSols

/-- The inclusion of anomaly free solutions into all charges. -/
def solsIncl (χ : ACCSystem) : MulActionHom ℚ χ.Sols χ.charges :=
  MulActionHom.comp χ.quadSolsIncl χ.solsInclQuadSols

structure Hom (χ η : ACCSystem) where
  charges : χ.charges →ₗ[ℚ] η.charges
  anomalyFree : χ.Sols → η.Sols
  commute : charges ∘ χ.solsIncl = η.solsIncl ∘ anomalyFree

def Hom.comp {χ η ε : ACCSystem} (g : Hom η ε) (f : Hom χ η) : Hom χ ε where
  charges := LinearMap.comp g.charges f.charges
  anomalyFree := g.anomalyFree ∘ f.anomalyFree
  commute := by
    simp
    rw [Function.comp.assoc]
    rw [f.commute, ← Function.comp.assoc, g.commute, Function.comp.assoc]

end ACCSystem
