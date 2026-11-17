import ContinuousBilinear.FeedbackConeProof

namespace ContinuousBilinear.FeedbackData

open scoped Matrix
variable {d : ℕ}

abbrev liftState {d : ℕ} (z : State d) : State (d + 1) := Fin.cases 0 z
abbrev scalarAxis (d : ℕ) : State (d + 1) := Fin.cases 1 0

/-- The off-diagonal part of a shear from the scalar axis into the state space. -/
def shearToState (w : State d) : RealMatrix (d + 1) :=
  Matrix.vecMulVec (liftState w) (scalarAxis d)

/-- The off-diagonal part of a shear from the state space into the scalar axis. -/
def shearToScalar (eta : State d) : RealMatrix (d + 1) :=
  Matrix.vecMulVec (scalarAxis d) (liftState eta)

private theorem dotProduct_liftState (x y : State d) :
    dotProduct (liftState x) (liftState y) = dotProduct x y := by
  simp [dotProduct, Fin.sum_univ_succ]

private theorem dotProduct_scalarAxis_liftState (x : State d) :
    dotProduct (scalarAxis d) (liftState x) = 0 := by
  simp [dotProduct, Fin.sum_univ_succ]

private theorem dotProduct_liftState_scalarAxis (x : State d) :
    dotProduct (liftState x) (scalarAxis d) = 0 := by
  simp [dotProduct, Fin.sum_univ_succ]

private theorem dotProduct_scalarAxis (d : ℕ) : dotProduct (scalarAxis d) (scalarAxis d) = 1 := by
  simp [dotProduct, Fin.sum_univ_succ]

theorem shearToState_sq (w : State d) : shearToState w * shearToState w = 0 := by
  simp [shearToState, Matrix.vecMulVec_mul_vecMulVec, dotProduct_scalarAxis_liftState]

theorem shearToScalar_sq (eta : State d) : shearToScalar eta * shearToScalar eta = 0 := by
  simp [shearToScalar, Matrix.vecMulVec_mul_vecMulVec, dotProduct_liftState_scalarAxis]

theorem shearToState_mul_shearToScalar_mul_shearToState (w eta : State d) :
    shearToState w * shearToScalar eta * shearToState w = dotProduct eta w • shearToState w := by
  simp [shearToState, shearToScalar, Matrix.vecMulVec_mul_vecMulVec, dotProduct_scalarAxis,
    dotProduct_liftState, Matrix.vecMulVec_smul]

theorem shearToScalar_mul_shearToState_mul_shearToScalar (w eta : State d) :
    shearToScalar eta * shearToState w * shearToScalar eta = dotProduct eta w • shearToScalar eta := by
  simp [shearToState, shearToScalar, Matrix.vecMulVec_mul_vecMulVec, dotProduct_scalarAxis,
    dotProduct_liftState, Matrix.vecMulVec_smul, smul_mul_assoc]

end ContinuousBilinear.FeedbackData
