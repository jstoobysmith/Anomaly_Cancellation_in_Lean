
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic.Ring
universe v u
open Nat

structure oneFamilyCharge where
  Q : ℚ
  U : ℚ
  D : ℚ
  L : ℚ
  E : ℚ
  N : ℚ

namespace oneFamilyCharge

@[ext]
theorem ext {a b : oneFamilyCharge}
    (hQ : a.Q = b.Q)
    (hU : a.U = b.U)
    (hD : a.D = b.D)
    (hL : a.L = b.L)
    (hE : a.E = b.E)
    (hN : a.N = b.N) :
    a = b := by
  cases' a
  simp_all only

end oneFamilyCharge

@[simps!]
def oneFamilyHyperCharge : oneFamilyCharge where
  Q := 1
  U := -4
  D := 2
  L := -3
  E := 6
  N := 0

structure threeFamilyCharge where
  Q1 : ℚ
  Q2 : ℚ
  Q3 : ℚ
  U1 : ℚ
  U2 : ℚ
  U3 : ℚ
  D1 : ℚ
  D2 : ℚ
  D3 : ℚ
  L1 : ℚ
  L2 : ℚ
  L3 : ℚ
  E1 : ℚ
  E2 : ℚ
  E3 : ℚ
  N1 : ℚ
  N2 : ℚ
  N3 : ℚ

namespace threeFamilyCharge

@[ext]
theorem ext {a b : threeFamilyCharge}
    (hQ1 : a.Q1 = b.Q1) (hQ2 : a.Q2 = b.Q2) (hQ3 : a.Q3 = b.Q3)
    (hU1 : a.U1 = b.U1) (hU2 : a.U2 = b.U2) (hU3 : a.U3 = b.U3)
    (hD1 : a.D1 = b.D1) (hD2 : a.D2 = b.D2) (hD3 : a.D3 = b.D3)
    (hL1 : a.L1 = b.L1) (hL2 : a.L2 = b.L2) (hL3 : a.L3 = b.L3)
    (hE1 : a.E1 = b.E1) (hE2 : a.E2 = b.E2) (hE3 : a.E3 = b.E3)
    (hN1 : a.N1 = b.N1) (hN2 : a.N2 = b.N2) (hN3 : a.N3 = b.N3):
    a = b := by
  cases' a
  simp_all only

end threeFamilyCharge

@[simps!]
def threeFamilyChargeAdd (X Y : threeFamilyCharge) : threeFamilyCharge :=
   {
    Q1 := X.Q1 + Y.Q1
    Q2 := X.Q2 + Y.Q2
    Q3 := X.Q3 + Y.Q3
    U1 := X.U1 + Y.U1
    U2 := X.U2 + Y.U2
    U3 := X.U3 + Y.U3
    D1 := X.D1 + Y.D1
    D2 := X.D2 + Y.D2
    D3 := X.D3 + Y.D3
    L1 := X.L1 + Y.L1
    L2 := X.L2 + Y.L2
    L3 := X.L3 + Y.L3
    E1 := X.E1 + Y.E1
    E2 := X.E2 + Y.E2
    E3 := X.E3 + Y.E3
    N1 := X.N1 + Y.N1
    N2 := X.N2 + Y.N2
    N3 := X.N3 + Y.N3
  }

@[simps!]
def threeFamilyChargeZero : threeFamilyCharge :=
   {
    Q1 := 0
    Q2 := 0
    Q3 := 0
    U1 := 0
    U2 := 0
    U3 := 0
    D1 := 0
    D2 := 0
    D3 := 0
    L1 := 0
    L2 := 0
    L3 := 0
    E1 := 0
    E2 := 0
    E3 := 0
    N1 := 0
    N2 := 0
    N3 := 0
  }

@[simps!]
def threeFamilyChargeSMul (a : ℚ) (X : threeFamilyCharge) : threeFamilyCharge :=
   {
    Q1 := a * X.Q1
    Q2 := a * X.Q2
    Q3 := a * X.Q3
    U1 := a * X.U1
    U2 := a * X.U2
    U3 := a * X.U3
    D1 := a * X.D1
    D2 := a * X.D2
    D3 := a * X.D3
    L1 := a * X.L1
    L2 := a * X.L2
    L3 := a * X.L3
    E1 := a * X.E1
    E2 := a * X.E2
    E3 := a * X.E3
    N1 := a * X.N1
    N2 := a * X.N2
    N3 := a * X.N3
  }

@[simps!]
instance threeFamilyChargeAddCommMonoid : AddCommMonoid threeFamilyCharge where
  add X Y := threeFamilyChargeAdd X Y
  add_assoc := by
    intro a b c
    apply threeFamilyCharge.ext <;> exact Rat.add_assoc _ _ _
  zero := threeFamilyChargeZero
  zero_add := by
    intro a
    apply threeFamilyCharge.ext <;> exact Rat.zero_add _
  add_zero := by
    intro a
    apply threeFamilyCharge.ext <;> exact Rat.add_zero _
  add_comm := by
    intro a b
    apply threeFamilyCharge.ext <;> exact Rat.add_comm _ _

@[simps!]
instance threeFamilyChargeModule : Module ℚ threeFamilyCharge where
  smul := threeFamilyChargeSMul
  one_smul := by
    intro b
    apply threeFamilyCharge.ext <;> exact Rat.one_mul _
  mul_smul := by
    intro x y b
    apply threeFamilyCharge.ext <;> exact Rat.mul_assoc _ _ _
  smul_zero := by
    intro x
    apply threeFamilyCharge.ext <;> exact Rat.mul_zero _
  zero_smul := by
    intro x
    apply threeFamilyCharge.ext <;> exact Rat.zero_mul _
  smul_add := by
    intro x a b
    apply threeFamilyCharge.ext <;> exact Rat.mul_add _ _ _
  add_smul := by
    intro x a b
    apply threeFamilyCharge.ext <;> exact Rat.add_mul _ _ _

@[simps!]
def oneFamilyToThreeFamily (S : oneFamilyCharge) : threeFamilyCharge :=
  ⟨S.Q, S.Q, S.Q, S.U, S.U, S.U, S.D, S.D, S.D, S.L, S.L, S.L, S.E, S.E, S.E, S.N, S.N, S.N⟩

@[simps!]
def hyperCharge : threeFamilyCharge := oneFamilyToThreeFamily oneFamilyHyperCharge

/-- The anomaly cancelation condition for the gravity anomaly. -/
@[simp]
def accGrav (S : threeFamilyCharge) : ℚ :=
  6 * (S.Q1 + S.Q2 + S.Q3)
  + 3 * (S.U1 + S.U2 + S.U3)
  + 3 * (S.D1 + S.D2 + S.D3)
  + 2 * (S.L1 + S.L2 + S.L3)
  + (S.E1 + S.E2 + S.E3)
  + (S.N1 + S.N2 + S.N3)

@[simp]
lemma accGrav_add (S T : threeFamilyCharge) :
    accGrav (S + T) = accGrav S + accGrav T := by
  simp [accGrav]
  ring

@[simp]
lemma accGrav_smul (a : ℚ) (S : threeFamilyCharge) :
    accGrav (a • S) = a * accGrav S := by
  simp [accGrav, HSMul.hSMul]
  ring

/-- The anomaly cancelation condition for SU(2) anomaly. -/
@[simp]
def accSU2 (S : threeFamilyCharge) : ℚ :=
  3 * (S.Q1 + S.Q2 + S.Q3)
  + (S.L1 + S.L2 + S.L3)

@[simp]
lemma accSU2_add (S T : threeFamilyCharge) :
    accSU2 (S + T) = accSU2 S + accSU2 T := by
  simp
  ring

@[simp]
lemma accSU2_smul (a : ℚ) (S : threeFamilyCharge) :
    accSU2 (a • S) = a * accSU2 S := by
  simp [HSMul.hSMul]
  ring

/-- The anomaly cancelation condition for SU(3) anomaly. -/
@[simp]
def accSU3 (S : threeFamilyCharge) : ℚ :=
  2 * (S.Q1 + S.Q2 + S.Q3)
  + (S.U1 + S.U2 + S.U3)
  + (S.D1 + S.D2 + S.D3)

@[simp]
lemma accSU3_add (S T : threeFamilyCharge) :
    accSU3 (S + T) = accSU3 S + accSU3 T := by
  simp
  ring

@[simp]
lemma accSU3_smul (a : ℚ) (S : threeFamilyCharge) :
    accSU3 (a • S) = a * accSU3 S := by
  simp [HSMul.hSMul]
  ring

/-- The anomaly cancelation condition for Y² anomaly. -/
@[simp]
def accYY (S : threeFamilyCharge) : ℚ :=
  (S.Q1 + S.Q2 + S.Q3)
  + 8 * (S.U1 + S.U2 + S.U3)
  + 2 * (S.D1 + S.D2 + S.D3)
  + 3 * (S.L1 + S.L2 + S.L3)
  + 6 * (S.E1 + S.E2 + S.E3)

@[simp]
lemma accYY_add (S T : threeFamilyCharge) :
    accYY (S + T) = accYY S + accYY T := by
  simp
  ring

@[simp]
lemma accYY_smul (a : ℚ) (S : threeFamilyCharge) :
    accYY (a • S) = a * accYY S := by
  simp [HSMul.hSMul]
  ring


/-- The anomaly cancelation condition for Y anomaly. -/
@[simp]
def accQuad (S : threeFamilyCharge) : ℚ :=
  (S.Q1^2 + S.Q2^2 + S.Q3^2)
  - 2 * (S.U1^2 + S.U2^2 + S.U3^2)
  + (S.D1^2 + S.D2^2 + S.D3^2)
  - (S.L1^2 + S.L2^2 + S.L3^2)
  + (S.E1^2 + S.E2^2 + S.E3^2)

@[simp]
def accQuadDiv (S T : threeFamilyCharge) : ℚ :=
  2 * ((T.Q1 * S.Q1 + T.Q2 * S.Q2 + T.Q3 * S.Q3)
  - 2 * (T.U1 * S.U1 + T.U2 * S.U2 + T.U3 * S.U3)
  + (T.D1 * S.D1 + T.D2 * S.D2 + T.D3 * S.D3)
  - (T.L1 * S.L1 + T.L2 * S.L2 + T.L3 * S.L3)
  + (T.E1 * S.E1 + T.E2 * S.E2 + T.E3 * S.E3))

lemma accQuadDiv_hyperCharge (S : threeFamilyCharge) :
    accQuadDiv hyperCharge S = 2 * accYY S := by
  simp [hyperCharge, oneFamilyHyperCharge]
  ring

lemma accQuadDiv_symm : accQuadDiv S T = accQuadDiv T S := by
  simp
  ring

lemma accQuad_add (S T : threeFamilyCharge) :
    accQuad (S + T) = accQuad S + accQuadDiv S T + accQuad T := by
  simp
  ring_nf


@[simp]
lemma accQuad_smul (a : ℚ) (S : threeFamilyCharge) :
    accQuad (a • S) = a^2 * accQuad S := by
  simp [HSMul.hSMul]
  ring

/-- The anomaly cancelation condition for Y anomaly. -/
@[simp]
def accCube (S : threeFamilyCharge) : ℚ :=
  6 * (S.Q1^3 + S.Q2^3 + S.Q3^3)
  + 3 * (S.U1^3 + S.U2^3 + S.U3^3)
  + 3 * (S.D1^3 + S.D2^3 + S.D3^3)
  + 2 * (S.L1^3 + S.L2^3 + S.L3^3)
  + (S.E1^3 + S.E2^3 + S.E3^3)
  + (S.N1^3 + S.N2^3 + S.N3^3)

@[simp]
lemma accCube_smul (a : ℚ) (S : threeFamilyCharge) :
    accCube (a • S) = a^3 * accCube S := by
  simp [HSMul.hSMul]
  ring

/-- The class of charges which satisfy the linear ACCs. -/
structure AnomalyFreeLinear where
  val : threeFamilyCharge
  Grav : accGrav val = 0
  SU2 : accSU2 val = 0
  SU3 : accSU3 val = 0
  YY  : accYY val = 0

@[ext]
lemma AnomalyFreeLinear.ext {S T : AnomalyFreeLinear} (h : S.val = T.val) : S = T := by
  cases' S
  simp_all only

def hyperChargeLinear : AnomalyFreeLinear :=
  ⟨hyperCharge, by rfl, by rfl , by rfl, by rfl⟩

@[simps!]
instance AnomalyFreeLinearAdd : AddCommMonoid AnomalyFreeLinear where
  add S T := ⟨S.val + T.val,
    by rw [accGrav_add, S.Grav, T.Grav, Rat.zero_add],
    by rw [accSU2_add, S.SU2, T.SU2, Rat.zero_add],
    by rw [accSU3_add, S.SU3, T.SU3, Rat.zero_add],
    by rw [accYY_add, S.YY, T.YY, Rat.zero_add]⟩
  add_assoc S T L := by
    apply AnomalyFreeLinear.ext
    exact threeFamilyChargeAddCommMonoid.add_assoc _ _ _
  zero := ⟨threeFamilyChargeAddCommMonoid.zero, by rfl, by rfl, by rfl, by rfl⟩
  zero_add S := by
    apply AnomalyFreeLinear.ext
    exact threeFamilyChargeAddCommMonoid.zero_add _
  add_zero S := by
    apply AnomalyFreeLinear.ext
    exact threeFamilyChargeAddCommMonoid.add_zero _
  add_comm S T := by
    apply AnomalyFreeLinear.ext
    exact threeFamilyChargeAddCommMonoid.add_comm _ _

@[simps!]
instance AnomalyFreeLinearModule : Module ℚ AnomalyFreeLinear where
  smul a S := ⟨a • S.val,
    by rw [accGrav_smul, S.Grav, Rat.mul_zero],
    by rw [accSU2_smul, S.SU2, Rat.mul_zero],
    by rw [accSU3_smul, S.SU3, Rat.mul_zero],
    by rw [accYY_smul, S.YY, Rat.mul_zero]⟩
  one_smul _ := by
    apply AnomalyFreeLinear.ext
    exact threeFamilyChargeModule.one_smul _
  mul_smul _ _ _ := by
    apply AnomalyFreeLinear.ext
    exact threeFamilyChargeModule.mul_smul _ _ _
  smul_zero _ := by
    apply AnomalyFreeLinear.ext
    exact threeFamilyChargeModule.smul_zero _
  smul_add _ _ _ := by
    apply AnomalyFreeLinear.ext
    exact threeFamilyChargeModule.smul_add _ _ _
  add_smul _ _ _ := by
    apply AnomalyFreeLinear.ext
    exact threeFamilyChargeModule.add_smul _ _ _
  zero_smul _ := by
    apply AnomalyFreeLinear.ext
    exact threeFamilyChargeModule.zero_smul _

structure AnomalyFree where
  val : AnomalyFreeLinear
  Quad : accQuad val.val = 0
  Cube : accCube val.val = 0

/-- The scalar multiple of any solution is also a solution. -/
def AnomalyFreeSMul (a : ℚ) (S : AnomalyFree) : AnomalyFree :=
  ⟨a • S.val,
    by erw [accQuad_smul, S.Quad, Rat.mul_zero],
    by erw [accCube_smul, S.Cube, Rat.mul_zero]⟩
