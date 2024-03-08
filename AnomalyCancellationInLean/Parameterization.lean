import AnomalyCancellationInLean.BMinusL
import Mathlib.Tactic.Polyrith

section linearParameters

structure linearParameters where
  Q1 : ℚ
  Q2 : ℚ
  U1 : ℚ
  U2 : ℚ
  D1 : ℚ
  D2 : ℚ
  D3 : ℚ
  L1 : ℚ
  L2 : ℚ
  E1 : ℚ
  E2 : ℚ
  N1 : ℚ
  N2 : ℚ
  N3 : ℚ

def linearParameterization : linearParameters ≃ AnomalyFreeLinear where
  toFun := fun S =>
    ⟨⟨S.Q1, S.Q2, 1/2 * (-2 * S.Q1 - 2 * S.Q2 + (S.D1 + S.D2 + S.D3) + (S.N1 + S.N2 + S.N3)),
      S.U1, S.U2, - (S.U1 + S.U2 + 2 * (S.D1 + S.D2 + S.D3) + (S.N1 + S.N2 + S.N3)),
      S.D1, S.D2, S.D3,
      S.L1, S.L2, -1/2 * (2 * S.L1 + 2 * S.L2 +  3 * (S.D1 + S.D2 + S.D3) +
        3 * (S.N1 + S.N2 + S.N3)),
      S.E1, S.E2, - (S.E1 + S.E2 - 3 * (S.D1 + S.D2 + S.D3) - 2 * (S.N1 + S.N2 + S.N3) ),
      S.N1, S.N2, S.N3⟩,
      by simp; ring, by simp; ring, by simp; ring, by simp; ring⟩
  invFun := fun S =>
    ⟨S.1.Q1, S.1.Q2, S.1.U1, S.1.U2, S.1.D1, S.1.D2, S.1.D3, S.1.L1,
     S.1.L2, S.1.E1, S.1.E2, S.1.N1, S.1.N2, S.1.N3⟩
  left_inv := by
    intro S
    rfl
  right_inv := by
    intro S
    apply AnomalyFreeLinear.ext
    have hS1 := S.Grav
    have hS2 := S.SU2
    have hS3 := S.SU3
    have hS4 := S.YY
    simp_all
    apply threeFamilyCharge.ext
    any_goals simp
    -- The below can be found using polyrith.
    linear_combination hS1 / 2 - 3 / 4 * hS2 - 5 / 6 * hS3 + -1 * hS4 / 12
    linear_combination -(1 * hS1) + 3 / 2 * hS2 + 2 / 3 * hS3 + hS4 / 6
    linear_combination -(3 / 2 * hS1) + 5 / 4 * hS2 + 5 / 2 * hS3 + hS4 / 4
    linear_combination 2 * hS1 - 5 / 2 * hS2 - 2 * hS3 + -1 * hS4 / 2






end linearParameters

section mapToQuad

def mapToQuadPointPt : threeFamilyCharge :=
  ⟨-1, 0, 1, -1, 0, 1, -1, 0, 1, -1, 0, 1, -1, 0, 1, 0, 0, 0⟩

def mapToQuadPoint : AnomalyFree :=
  ⟨⟨⟨mapToQuadPointPt, by rfl, by rfl, by rfl, by rfl⟩, by rfl⟩, by rfl⟩

def mapToQuadGeneric (S : AnomalyFreeLinear) : AnomalyFreeQuad :=
  ⟨(accQuad S.val) • mapToQuadPoint.val.val +
    (- 2 * (accQuadDiv mapToQuadPoint.val.val.val S.val)) • S
   , by
    erw [accQuad_add, accQuad_smul, accQuad_smul]
    rw [mapToQuadPoint.val.Quad]
    simp only [mul_zero, neg_mul, zero_add]
    erw [accQuadDiv_smul_left]
    erw [accQuadDiv_smul_left]
    ring⟩

lemma mapToQuadGeneric_on_quad  (S : AnomalyFreeQuad) :
    mapToQuadGeneric S.val =
     AnomalyFreeQuadSmul (- 2 * (accQuadDiv mapToQuadPoint.val.val.val S.val.val)) S := by
  rw [mapToQuadGeneric]
  apply AnomalyFreeQuad.ext
  simp only
  rw [S.Quad, zero_smul, zero_add]
  rfl

def mapToQuadSpecial (S : AnomalyFreeLinear) (hSS : accQuad S.val = 0)
    (hCS : accQuadDiv mapToQuadPoint.val.val.val S.val = 0) (a b : ℚ) : AnomalyFreeQuad :=
  ⟨ a • mapToQuadPoint.val.val + b • S, by
    erw [accQuad_add, accQuad_smul, accQuad_smul]
    erw [accQuadDiv_smul_left]
    erw [accQuadDiv_smul_left]
    rw [hCS]
    rw [hSS]
    rw [mapToQuadPoint.val.Quad]
    simp⟩

@[simp]
def mapToQuad  : AnomalyFreeLinear × ℚ × ℚ → AnomalyFreeQuad :=  fun S =>
  if h : accQuad S.1.val = 0 ∧ accQuadDiv mapToQuadPoint.val.val.val S.1.val = 0 then
    mapToQuadSpecial S.1 h.left h.right S.2.1 S.2.2
  else
    AnomalyFreeQuadSmul S.2.1 (mapToQuadGeneric S.1)

theorem mapToQuad_surjective : Function.Surjective mapToQuad := by
  intro S
  by_cases hS :  accQuad S.val.val = 0 ∧ accQuadDiv mapToQuadPoint.val.val.val S.val.val = 0
  · use ⟨S.val, ⟨0, 1⟩⟩
    rw [mapToQuad]
    rw [dif_pos hS]
    rw [mapToQuadSpecial]
    apply AnomalyFreeQuad.ext
    simp only [zero_smul, one_smul, zero_add]
  · use ⟨S.val, ⟨1/((-2 * accQuadDiv mapToQuadPoint.val.val.val S.val.val)), 0⟩⟩
    rw [mapToQuad]
    rw [dif_neg hS]
    rw [mapToQuadGeneric_on_quad]
    rw [← AnomalyFreeQuad_mul_smul]
    rw [div_mul]
    rw [one_div_div]
    rw [div_self, AnomalyFreeQuad_one_smul]
    rw [S.Quad] at hS
    simp_all only [accQuadDiv, true_and, neg_mul, ne_eq, neg_eq_zero, _root_.mul_eq_zero,
      OfNat.ofNat_ne_zero, or_self, not_false_eq_true]

end mapToQuad

section mapToCube

def mapToCubeGeneric (S : AnomalyFreeQuad) : AnomalyFree :=
  ⟨AnomalyFreeQuadAddBMinusL (accCube S.val.val)
  (AnomalyFreeQuadSmul (- 3 * accCubeDiv BMinusL.val.val.val S.val.val) S),
  by
   simp only [AnomalyFreeQuadAddBMinusL, AnomalyFreeQuadSmul, HAdd.hAdd]
   simp only [Add.add]
   simp only [HSMul.hSMul]
   simp only [SMul.smul]
   rw [accCube_add, accCube_smul, accCube_smul, accCubeDiv_smul_left,
   accCubeDiv_smul_left, accCubeDiv_smul_right, accCubeDiv_smul_right]
   rw [BMinusL.Cube, accCubeDiv_AnomalyFreeLinear_BMinusL]
   ring
  ⟩

lemma mapToCubeGeneric_on_cube (S : AnomalyFree) :
    mapToCubeGeneric S.val =
     AnomalyFreeSMul (- 3 * accCubeDiv BMinusL.val.val.val S.val.val.val) S := by
  rw [mapToCubeGeneric]
  apply AnomalyFree.ext
  simp only
  rw [S.Cube]
  rw [AnomalyFreeQuadAddBMinusL_zero]
  rfl


def mapToCubeSpecial (S : AnomalyFreeQuad) (hSSS : accCube S.val.val = 0)
    (hB : accCubeDiv BMinusL.val.val.val S.val.val = 0) (a b : ℚ) : AnomalyFree :=
  ⟨AnomalyFreeQuadAddBMinusL a (AnomalyFreeQuadSmul b S), by
   simp only [AnomalyFreeQuadAddBMinusL, AnomalyFreeQuadSmul, HAdd.hAdd]
   simp only [Add.add]
   simp only [HSMul.hSMul]
   simp only [SMul.smul]
   rw [accCube_add, accCube_smul, accCube_smul, accCubeDiv_smul_left,
   accCubeDiv_smul_left, accCubeDiv_smul_right, accCubeDiv_smul_right]
   rw [BMinusL.Cube, hSSS, accCubeDiv_AnomalyFreeLinear_BMinusL, hB]
   simp only [mul_zero, add_zero]
  ⟩

@[simp]
def mapToCube : AnomalyFreeQuad × ℚ × ℚ → AnomalyFree :=  fun S =>
  if h : accCube S.1.val.val = 0 ∧ accCubeDiv BMinusL.val.val.val S.1.val.val = 0 then
    mapToCubeSpecial S.1 h.left h.right S.2.1 S.2.2
  else
    AnomalyFreeSMul S.2.1 (mapToCubeGeneric S.1)

theorem mapToCube_surjective : Function.Surjective mapToCube := by
  intro S
  by_cases hS :  accCube S.val.val.val = 0 ∧ accCubeDiv BMinusL.val.val.val S.val.val.val = 0
  · use ⟨S.val, ⟨0, 1⟩⟩
    rw [mapToCube]
    rw [dif_pos hS]
    rw [mapToCubeSpecial]
    apply AnomalyFree.ext
    simp [AnomalyFreeQuadAddBMinusL, AnomalyFreeQuadSmul]
  · use ⟨S.val, ⟨1/((-3 * accCubeDiv BMinusL.val.val.val S.val.val.val)), 0⟩⟩
    rw [mapToCube]
    rw [dif_neg hS]
    rw [mapToCubeGeneric_on_cube]
    rw [← AnomalyFree_mul_smul]
    rw [div_mul]
    rw [one_div_div]
    rw [div_self, AnomalyFree_one_smul]
    rw [S.Cube] at hS
    simp_all only [accCubeDiv, true_and, neg_mul, ne_eq, neg_eq_zero, _root_.mul_eq_zero,
      OfNat.ofNat_ne_zero, or_self, not_false_eq_true]

end mapToCube
structure parameters where
  lin : linearParameters
  a : ℚ
  b : ℚ
  c : ℚ
  d : ℚ

@[ext]
lemma parameters.ext {P1 P2 : parameters} (hlin : P1.lin = P2.lin)
    (ha : P1.a = P2.a) (hb : P1.b = P2.b) (hc : P1.c = P2.c) (hd : P1.d = P2.d) : P1 = P2 := by
  cases' P1
  simp_all

def  parametersEquiv : parameters ≃ AnomalyFreeLinear × ℚ × ℚ × ℚ × ℚ  where
  toFun := fun S =>
    ⟨linearParameterization.toFun S.1, ⟨S.a, ⟨S.b, ⟨S.c, S.d⟩⟩⟩⟩
  invFun := fun S => ⟨linearParameterization.invFun S.1, S.2.1, S.2.2.1, S.2.2.2.1, S.2.2.2.2⟩
  left_inv := by
    intro P
    ext
    exact linearParameterization.left_inv _
    rfl
    rfl
    rfl
    rfl
  right_inv := by
    intro P
    apply Prod.ext
    exact linearParameterization.right_inv _
    rfl


def map' : AnomalyFreeLinear × ℚ × ℚ × ℚ × ℚ → AnomalyFree := fun S =>
  mapToCube ⟨mapToQuad ⟨S.1, ⟨S.2.1, S.2.2.1⟩⟩, ⟨S.2.2.2.1, S.2.2.2.2⟩⟩

lemma map'_surjective : Function.Surjective map' := by
  intro S
  obtain ⟨S1, hS1⟩ := mapToCube_surjective S
  obtain ⟨S2, hS2⟩ := mapToQuad_surjective S1.1
  use ⟨S2.1, ⟨S2.2.1, ⟨S2.2.2, S1.2⟩⟩⟩
  change mapToCube ⟨mapToQuad S2, _⟩ = _
  rw [hS2]
  exact hS1

def map : parameters → AnomalyFree := map' ∘ parametersEquiv.toFun

theorem map_surjective : Function.Surjective map :=
  Function.Surjective.comp (map'_surjective) (Equiv.surjective _)
