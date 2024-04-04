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

structure ACCSystemCharges where
  numberCharges : ℕ


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

structure AnomalyFreeLinear (χ : ACCSystemLinear) where
  val : χ.1.charges
  linearSol : ∀ i : Fin χ.numberLinear, χ.linearACCs i val = 0

@[ext]
lemma AnomalyFreeLinear.ext {χ : ACCSystemLinear} {S T : χ.AnomalyFreeLinear} (h : S.val = T.val) :
    S = T := by
  cases' S
  simp_all only

@[simps!]
instance AnomalyFreeLinearAddCommMonoid (χ : ACCSystemLinear) :
    AddCommMonoid χ.AnomalyFreeLinear where
  add S T := ⟨S.val + T.val, by
    intro i
    rw [(χ.linearACCs i).map_add, S.linearSol i, T.linearSol i]
    rfl⟩
  add_comm S T := by
    apply AnomalyFreeLinear.ext
    exact χ.chargesAddCommMonoid.add_comm _ _
  add_assoc S T L := by
    apply AnomalyFreeLinear.ext
    exact χ.chargesAddCommMonoid.add_assoc _ _ _
  zero := ⟨χ.chargesAddCommMonoid.zero, by
    intro i
    erw [(χ.linearACCs i).map_zero]⟩
  zero_add S := by
    apply AnomalyFreeLinear.ext
    exact χ.chargesAddCommMonoid.zero_add _
  add_zero S := by
    apply AnomalyFreeLinear.ext
    exact χ.chargesAddCommMonoid.add_zero _
  nsmul n S := ⟨n  • S.val, by
    intro i
    rw [nsmul_eq_smul_cast ℚ]
    erw [(χ.linearACCs i).map_smul, S.linearSol i]
    simp⟩
  nsmul_zero n := by
    rfl
  nsmul_succ n S := by
    apply AnomalyFreeLinear.ext
    exact χ.chargesAddCommMonoid.nsmul_succ _ _

@[simps!]
instance AnomalyFreeLinearAddCommModule  (χ : ACCSystemLinear) : Module ℚ χ.AnomalyFreeLinear where
  smul a S := ⟨a • S.val, by
    intro i
    rw [(χ.linearACCs i).map_smul, S.linearSol i]
    simp⟩
  one_smul one_smul := by
    apply AnomalyFreeLinear.ext
    exact χ.chargesModule.one_smul _
  mul_smul a b S := by
    apply AnomalyFreeLinear.ext
    exact χ.chargesModule.mul_smul _ _ _
  smul_zero a := by
    apply AnomalyFreeLinear.ext
    exact χ.chargesModule.smul_zero _
  zero_smul S := by
    apply AnomalyFreeLinear.ext
    exact χ.chargesModule.zero_smul _
  smul_add a S T := by
    apply AnomalyFreeLinear.ext
    exact χ.chargesModule.smul_add _ _ _
  add_smul a b T:= by
    apply AnomalyFreeLinear.ext
    exact χ.chargesModule.add_smul _ _ _

instance AnomalyFreeLinearAddCommGroup (χ : ACCSystemLinear) :
    AddCommGroup χ.AnomalyFreeLinear :=
  Module.addCommMonoidToAddCommGroup ℚ

/-- The linear map reperesenting the
 inclusion of charges satisfying the linear anomaly free equations into all charges. -/
def anomalyFreeLinearIncl  (χ : ACCSystemLinear) :
    χ.AnomalyFreeLinear →ₗ[ℚ] χ.charges where
  toFun S := S.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


end ACCSystemLinear


structure ACCSystemQuad extends ACCSystemLinear where
  numberQuadratic : ℕ
  quadraticACCs : Fin numberQuadratic → HomogeneousQuadratic toACCSystemCharges.charges


namespace ACCSystemQuad

structure AnomalyFreeQuad (χ : ACCSystemQuad) extends χ.AnomalyFreeLinear where
  quadSol : ∀ i : Fin χ.numberQuadratic, (χ.quadraticACCs i) val = 0

@[ext]
lemma AnomalyFreeQuad.ext {χ : ACCSystemQuad} {S T : χ.AnomalyFreeQuad} (h : S.val = T.val) :
    S = T := by
  have h  := ACCSystemLinear.AnomalyFreeLinear.ext h
  cases' S
  simp_all only

/-- The scalar multiple of any solution to the linear + quadratic equations is still a solution. -/
instance AnomalyFreeQuadMulAction (χ : ACCSystemQuad) : MulAction ℚ χ.AnomalyFreeQuad where
  smul a S :=  ⟨a • S.toAnomalyFreeLinear , by
    intro i
    erw [(χ.quadraticACCs i).map_smul]
    rw [S.quadSol i]
    simp
    ⟩
  mul_smul a b S := by
    apply AnomalyFreeQuad.ext
    exact mul_smul _ _ _
  one_smul S := by
    apply AnomalyFreeQuad.ext
    exact one_smul _ _

def AnomalyFreeQuadInclLinear (χ : ACCSystemQuad) :
    MulActionHom ℚ χ.AnomalyFreeQuad χ.AnomalyFreeLinear  where
  toFun  := AnomalyFreeQuad.toAnomalyFreeLinear
  map_smul' _ _ := rfl


def AnomalyFreeQuadInv (χ : ACCSystemQuad) (h : χ.numberQuadratic = 0) :
    MulActionHom ℚ χ.AnomalyFreeLinear χ.AnomalyFreeQuad where
  toFun S := ⟨S, by intro i; rw [h] at i; exact Fin.elim0 i⟩
  map_smul' _ _ := rfl

def AnomalyFreeQuadIncl (χ : ACCSystemQuad) :
    MulActionHom ℚ χ.AnomalyFreeQuad χ.charges :=
  MulActionHom.comp χ.anomalyFreeLinearIncl  χ.AnomalyFreeQuadInclLinear

end ACCSystemQuad

structure ACCSystem extends ACCSystemQuad where
  cubicACC : HomogeneousCubic toACCSystemCharges.charges


namespace ACCSystem

structure AnomalyFree (χ : ACCSystem) extends χ.AnomalyFreeQuad where
  cubicSol : χ.cubicACC val = 0


lemma AnomalyFree.ext {χ : ACCSystem} {S T : χ.AnomalyFree} (h : S.val = T.val) :
    S = T := by
  have h  := ACCSystemQuad.AnomalyFreeQuad.ext h
  cases' S
  simp_all only

/-- The scalar multiple of any solution to the linear + quadratic equations is still a solution. -/
instance AnomalyFreeMulAction (χ : ACCSystem) : MulAction ℚ χ.AnomalyFree where
  smul a S :=  ⟨a • S.toAnomalyFreeQuad , by
    erw [(χ.cubicACC).map_smul]
    rw [S.cubicSol]
    simp
    ⟩
  mul_smul a b S := by
    apply AnomalyFree.ext
    exact mul_smul _ _ _
  one_smul S := by
    apply AnomalyFree.ext
    exact one_smul _ _

/-- The inclusion of the anomaly free solution into solutions of the quadratic and
linear equations -/
def AnomalyFreeInclQuad (χ : ACCSystem) :
    MulActionHom ℚ χ.AnomalyFree χ.AnomalyFreeQuad  where
  toFun  := AnomalyFree.toAnomalyFreeQuad
  map_smul' _ _ := rfl

/-- The inclusion of anomaly free solutions into all solutions of the linear equations. -/
def AnomalyFreeInclLinear (χ : ACCSystem) : MulActionHom ℚ χ.AnomalyFree χ.AnomalyFreeLinear :=
  MulActionHom.comp χ.AnomalyFreeQuadInclLinear χ.AnomalyFreeInclQuad

/-- The inclusion of anomaly free solutions into all charges. -/
def AnomalyFreeIncl (χ : ACCSystem) : MulActionHom ℚ χ.AnomalyFree χ.charges :=
  MulActionHom.comp χ.AnomalyFreeQuadIncl χ.AnomalyFreeInclQuad

structure Hom (χ η : ACCSystem) where
  charges : χ.charges →ₗ[ℚ] η.charges
  anomalyFree : χ.AnomalyFree → η.AnomalyFree
  commute : charges ∘ χ.AnomalyFreeIncl = η.AnomalyFreeIncl ∘ anomalyFree

def Hom.comp {χ η ε : ACCSystem} (g : Hom η ε) (f : Hom χ η) : Hom χ ε where
  charges := LinearMap.comp g.charges f.charges
  anomalyFree := g.anomalyFree ∘ f.anomalyFree
  commute := by
    simp
    rw [Function.comp.assoc]
    rw [f.commute, ← Function.comp.assoc, g.commute, Function.comp.assoc]



end ACCSystem
