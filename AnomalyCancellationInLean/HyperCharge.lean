import AnomalyCancellationInLean.Basics

@[simps!]
def oneFamilyHyperCharge : oneFamilyCharge :=
  ⟨1, -4, 2, -3, 6, 0⟩

@[simps!]
def hyperCharge : AnomalyFree :=
  ⟨⟨⟨oneFamilyToThreeFamily oneFamilyHyperCharge, by rfl, by rfl, by rfl, by rfl⟩, by rfl⟩, by rfl⟩

lemma accQuadDiv_hyperCharge (S : threeFamilyCharge) :
    accQuadDiv hyperCharge.1.1.1 S = accYY S := by
  simp [hyperCharge, oneFamilyHyperCharge]
  ring

lemma accCubeDiv_hyperCharge_of (S : threeFamilyCharge) :
    accCubeDiv hyperCharge.1.1.1 S = 6 * accQuad S := by
  simp [hyperCharge, oneFamilyHyperCharge]
  ring

@[simp]
lemma accCubeDiv_hyperCharge_AnomalyFreeLinear (S : AnomalyFreeQuad) :
    accCubeDiv hyperCharge.val.val.val S.val.val = 0 := by
  rw [accCubeDiv_hyperCharge_of, S.Quad]
  rfl

@[simp]
lemma accCubeDiv_of_hyperCharge (S : threeFamilyCharge) :
    accCubeDiv S hyperCharge.val.val.val = 6 * accYY S := by
  simp [hyperCharge, oneFamilyHyperCharge]
  ring

@[simp]
lemma accCubeDiv_AnomalyFreeLinear_hyperCharge (S : AnomalyFreeLinear) :
    accCubeDiv S.val hyperCharge.val.val.val = 0 := by
  rw [accCubeDiv_of_hyperCharge, S.YY]
  rfl

def AnomalyFreeQuadAddHyperCharge  (a : ℚ) (S : AnomalyFreeQuad) : AnomalyFreeQuad :=
   ⟨S.val + a • hyperCharge.val.val,
    by
      erw [accQuad_add, S.Quad, accQuad_smul, hyperCharge.val.Quad, accQuadDiv_smul_right,
      accQuadDiv_hyperCharge, S.val.YY]
      simp only [mul_zero, add_zero]⟩


def AnomalyFreeAddHyperCharge (a : ℚ) (S : AnomalyFree) : AnomalyFree :=
  ⟨AnomalyFreeQuadAddHyperCharge a S.val
    ,
    by
      rw [AnomalyFreeQuadAddHyperCharge]
      erw [accCube_add]
      rw [S.Cube]
      erw [accCubeDiv_smul_left]
      rw [accCubeDiv_hyperCharge_AnomalyFreeLinear]
      erw [accCubeDiv_smul_right]
      rw [accCubeDiv_AnomalyFreeLinear_hyperCharge]
      erw [accCube_smul]
      rw [hyperCharge.Cube]
      simp only [mul_zero, add_zero]⟩
