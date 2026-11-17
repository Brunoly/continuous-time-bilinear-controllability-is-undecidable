import ContinuousBilinear.PolynomialLiftComputableFull
import Mathlib.LinearAlgebra.Matrix.Reindex

namespace ContinuousBilinear
namespace PolynomialLift

open scoped BigOperators Matrix Matrix.Norms.Operator

private theorem exp_submatrix_equiv {n m : ℕ} (e : Fin m ≃ Fin n) (A : RealMatrix n) :
    NormedSpace.exp (A.submatrix e e) = (NormedSpace.exp A).submatrix e e := by
  let f := Matrix.reindexAlgEquiv ℝ ℝ e.symm
  have hf : Continuous f := f.toLinearMap.continuous_of_finiteDimensional
  exact (NormedSpace.map_exp f hf A).symm

/-- The finite tables compute the exact normalized scalar coefficient of the sign polynomial. -/
theorem compiledSign_matrix_coefficient (p : IntegerPolynomialCode) (u : SignChannel p → ℝ) :
    (∑ j, ((compiledSignOutput p) j : ℝ) *
      ((NormedSpace.exp (∑ i : Fin (p.arity + 2),
        u (oscillatorChannelAt (p.arity + 1) i) •
          (compiledSignMatrices p i).map (Int.castRingHom ℝ))).mulVec
        (fun j => ((compiledSignInitial p) j : ℝ))) j) =
      p.signPolynomialValue (fun i => u (some i)) (fun i => Real.sin (u (some i))) (u none) /
        ((signBaseValue p) : ℝ) := by
  let e : Fin (compilePolynomialLift p).1 ≃ Fin (signDimension p) := liftIndexEquiv p
  let compiledGenerator : RealMatrix (compilePolynomialLift p).1 :=
    ∑ i : Fin (p.arity + 2),
      u (oscillatorChannelAt (p.arity + 1) i) •
        (compiledSignMatrices p i).map (Int.castRingHom ℝ)
  let originalGenerator : RealMatrix (signDimension p) :=
    ∑ i, u i • (signMatrices p i).map (Int.castRingHom ℝ)
  have hg : compiledGenerator = originalGenerator.submatrix e e := by
    ext i j
    simp only [compiledGenerator, originalGenerator, Matrix.submatrix_apply, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.map_apply, compiledSignMatrices_entry]
    exact Fintype.sum_equiv (oscillatorChannelAt (p.arity + 1)) _ _ (fun _ => rfl)
  let b : State (signDimension p) := fun j => (signInitialVector p j : ℝ)
  have hb : (fun j => (compiledSignInitial p j : ℝ)) = b ∘ e := by
    funext j
    exact congrArg Int.cast (compiledSignInitial_entry p j)
  have hbInv : (b ∘ e) ∘ e.symm = b := by
    funext j
    simp [Function.comp_def]
  change (∑ j, ((compiledSignOutput p) j : ℝ) *
    ((NormedSpace.exp compiledGenerator).mulVec (fun j => (compiledSignInitial p j : ℝ))) j) = _
  rw [hg, exp_submatrix_equiv, hb, Matrix.submatrix_mulVec_equiv, hbInv]
  rw [← signPolynomial_matrix_coefficient p u]
  refine Fintype.sum_equiv e _ _ (fun i => ?_)
  simp only [compiledSignOutput_entry, Function.comp_apply]
  rfl

end PolynomialLift
end ContinuousBilinear
