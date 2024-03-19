/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license.
Authors: Joseph Tooby-Smith
-/
import AnomalyCancellationInLean.Basic
import Mathlib.RepresentationTheory.Basic

structure ACCSystemGroupAction (χ : ACCSystem) where
  group : Type
  groupInst : Group group
  rep : Representation ℚ group χ.charges
  linearInvariant : ∀ i g S, χ.linearACCs i (rep g S) = χ.linearACCs i S
  quadInvariant : ∀ i g S, (χ.quadraticACCs i).toFun (rep g S) = (χ.quadraticACCs i).toFun S
  cubicInvariant : ∀ g S, χ.cubicACC.toFun (rep g S) = χ.cubicACC.toFun S

namespace ACCSystemGroupAction

instance {χ : ACCSystem} (G : ACCSystemGroupAction χ) : Group G.group := G.groupInst


def anomalyFreeLinearMap {χ : ACCSystem} (G : ACCSystemGroupAction χ) (g : G.group) :
    χ.AnomalyFreeLinear →ₗ[ℚ] χ.AnomalyFreeLinear where
  toFun S := ⟨G.rep g S.val, by
   intro i
   rw [G.linearInvariant, S.linearSol]
   ⟩
  map_add' S T := by
    apply ACCSystemLinear.AnomalyFreeLinear.ext
    exact (G.rep g).map_add' _ _
  map_smul' a S := by
    apply ACCSystemLinear.AnomalyFreeLinear.ext
    exact (G.rep g).map_smul' _ _

@[simps!]
def repAnomalyFreeLinear {χ : ACCSystem} (G : ACCSystemGroupAction χ) :
    Representation ℚ G.group χ.AnomalyFreeLinear where
  toFun := G.anomalyFreeLinearMap
  map_mul' g1 g2 := by
    apply LinearMap.ext
    intro S
    apply ACCSystemLinear.AnomalyFreeLinear.ext
    change (G.rep.toFun (g1 * g2)) S.val = _
    rw [G.rep.map_mul']
    rfl
  map_one' := by
    apply LinearMap.ext
    intro S
    apply ACCSystemLinear.AnomalyFreeLinear.ext
    change (G.rep.toFun 1) S.val = _
    rw [G.rep.map_one']
    rfl

lemma rep_repAnomalyFreeLinear_commute {χ : ACCSystem} (G : ACCSystemGroupAction χ) (g : G.group)
    (S : χ.AnomalyFreeLinear) : χ.anomalyFreeLinearIncl (G.repAnomalyFreeLinear g S) =
    G.rep g (χ.anomalyFreeLinearIncl S) := rfl


instance actionAnomalyFreeQuad {χ : ACCSystem} (G : ACCSystemGroupAction χ) :
    MulAction G.group χ.AnomalyFreeQuad where
  smul f S := ⟨G.repAnomalyFreeLinear f S.1, by
   intro i
   simp
   rw [G.quadInvariant, S.quadSol]
  ⟩
  mul_smul f1 f2 S := by
    apply ACCSystemQuad.AnomalyFreeQuad.ext
    change (G.rep.toFun (f1 * f2)) S.val = _
    rw [G.rep.map_mul']
    rfl
  one_smul S := by
    apply ACCSystemQuad.AnomalyFreeQuad.ext
    change (G.rep.toFun 1) S.val = _
    rw [G.rep.map_one']
    rfl

lemma repAnomalyFreeLinear_actionAnomalyFreeQuad_commute {χ : ACCSystem}
    (G : ACCSystemGroupAction χ) (g : G.group)
    (S : χ.AnomalyFreeQuad) :  χ.AnomalyFreeQuadInclLinear (G.actionAnomalyFreeQuad.toFun S g) =
    G.repAnomalyFreeLinear g (χ.AnomalyFreeQuadInclLinear S) := rfl

lemma rep_actionAnomalyFreeQuad_commute {χ : ACCSystem}
    (G : ACCSystemGroupAction χ) (g : G.group)
    (S : χ.AnomalyFreeQuad) :  χ.AnomalyFreeQuadIncl (G.actionAnomalyFreeQuad.toFun S g) =
    G.rep g (χ.AnomalyFreeQuadIncl S) := rfl

instance actionAnomalyFree {χ : ACCSystem} (G : ACCSystemGroupAction χ) :
    MulAction G.group χ.AnomalyFree where
  smul g S := ⟨G.actionAnomalyFreeQuad.toFun S.1 g, by
   simp
   change χ.cubicACC.toFun (G.rep g S.val) = 0
   rw [G.cubicInvariant, S.cubicSol]
  ⟩
  mul_smul f1 f2 S := by
    apply ACCSystem.AnomalyFree.ext
    change (G.rep.toFun (f1 * f2)) S.val = _
    rw [G.rep.map_mul']
    rfl
  one_smul S := by
    apply ACCSystem.AnomalyFree.ext
    change (G.rep.toFun 1) S.val = _
    rw [G.rep.map_one']
    rfl

lemma actionAnomalyFreeQuad_actionAnomalyFree_commute {χ : ACCSystem}
    (G : ACCSystemGroupAction χ) (g : G.group)
    (S : χ.AnomalyFree) :  χ.AnomalyFreeInclQuad (G.actionAnomalyFree.toFun S g) =
    G.actionAnomalyFreeQuad.toFun (χ.AnomalyFreeInclQuad S) g := rfl

lemma repAnomalyFreeLinear_actionAnomalyFree_commute {χ : ACCSystem}
    (G : ACCSystemGroupAction χ) (g : G.group)
    (S : χ.AnomalyFree) :  χ.AnomalyFreeInclLinear (G.actionAnomalyFree.toFun S g) =
    G.repAnomalyFreeLinear g (χ.AnomalyFreeInclLinear S) := rfl

lemma rep_actionAnomalyFree_commute {χ : ACCSystem}
    (G : ACCSystemGroupAction χ) (g : G.group)
    (S : χ.AnomalyFree) :  χ.AnomalyFreeIncl (G.actionAnomalyFree.toFun S g) =
    G.rep g (χ.AnomalyFreeIncl S) := rfl

end ACCSystemGroupAction
