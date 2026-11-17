import ContinuousBilinear.PolynomialLiftComputableRational
import Mathlib.LinearAlgebra.Matrix.Reindex

namespace ContinuousBilinear
namespace PolynomialLift

/-- The rational matrices produced by the compiler commute pairwise. -/
theorem compileRationalLift_operators_commute (p : IntegerPolynomialCode)
    (k l : Fin (compileRationalLift p).2.2.2.length) :
    Commute ((compileRationalLift p).operator k) ((compileRationalLift p).operator l) := by
  let c := compileRationalLift p
  let e : Fin c.1 ≃ Fin (signDimension p) := liftIndexEquiv p
  let f : Matrix (Fin (signDimension p)) (Fin (signDimension p)) ℤ →+*
      Matrix (Fin c.1) (Fin c.1) ℚ :=
    (Int.castRingHom ℚ).mapMatrix.comp (Matrix.reindexAlgEquiv ℤ ℤ e.symm).toRingHom
  let channel := compiledRationalChannelEquiv p
  have h (a : Fin c.2.2.2.length) : c.operator a = f (signMatrices p (channel a)) := by
    ext i j
    let q := finCongr (compileRationalLift_channelCount p) a
    calc
      c.operator a i j = (compiledSignMatrices p q i j : ℚ) :=
        compileRationalLift_operator p a i j
      _ = f (signMatrices p (channel a)) i j :=
        congrArg (Int.cast : ℤ → ℚ) (compiledSignMatrices_entry p q i j)
  change Commute (c.operator k) (c.operator l)
  rw [h k, h l]
  exact (commute_signMatrices p (channel k) (channel l)).map f

end PolynomialLift
end ContinuousBilinear
