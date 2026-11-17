import ContinuousBilinear.PolynomialLiftQuotient

namespace ContinuousBilinear
namespace PolynomialLift

open scoped Matrix.Norms.Operator

noncomputable section

/-- Exponential flows respect linear intertwiners even between different dimensions. -/
theorem exp_mulVec_intertwining {n m : ℕ} (A : RealMatrix n) (B : RealMatrix m)
    (L : Matrix (Fin m) (Fin n) ℝ) (h : L * A = B * L) (x : State n) :
    L.mulVec ((NormedSpace.exp A).mulVec x) =
      (NormedSpace.exp B).mulVec (L.mulVec x) := by
  let f : State n →L[ℝ] State m := LinearMap.toContinuousLinearMap (Matrix.mulVecLin L)
  let z : ℝ → State m := fun t => L.mulVec ((NormedSpace.exp (t • A)).mulVec x)
  have h₀ : z 0 = L.mulVec x := by simp [z, NormedSpace.exp_zero]
  have hder (t : ℝ) : HasDerivAt z (B.mulVec (z t)) t := by
    have ht := f.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_exp_mulVec A x t)
    change HasDerivAt z
      (L.mulVec (A.mulVec ((NormedSpace.exp (t • A)).mulVec x))) t at ht
    have he : L.mulVec (A.mulVec ((NormedSpace.exp (t • A)).mulVec x)) =
        B.mulVec (z t) := by
      simp only [z, Matrix.mulVec_mulVec]
      rw [← Matrix.mul_assoc, h, Matrix.mul_assoc]
    exact he ▸ ht
  have he := eqOn_exp_mulVec_of_hasDerivWithinAt B (L.mulVec x) z 1 h₀
    (fun t _ => (hder t).hasDerivWithinAt)
  simpa only [z, one_smul] using he (show (1 : ℝ) ∈ Set.Icc 0 1 from ⟨zero_le_one, le_rfl⟩)

def realPencil {ι : Type*} [Fintype ι] {n : ℕ}
    (A : ι → Matrix (Fin n) (Fin n) ℚ) (u : ι → ℝ) : RealMatrix n :=
  ∑ i, u i • (A i).map (Rat.castHom ℝ)

theorem realPencil_intertwining {ι : Type*} [Fintype ι] {n m : ℕ}
    (A : ι → Matrix (Fin n) (Fin n) ℚ) (B : ι → Matrix (Fin m) (Fin m) ℚ)
    (L : Matrix (Fin m) (Fin n) ℚ) (h : ∀ i, L * A i = B i * L) (u : ι → ℝ) :
    L.map (Rat.castHom ℝ) * realPencil A u =
      realPencil B u * L.map (Rat.castHom ℝ) := by
  unfold realPencil
  rw [Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.map_mul, ← Matrix.map_mul, h i]

theorem exp_realPencil_mulVec_intertwining {ι : Type*} [Fintype ι] {n m : ℕ}
    (A : ι → Matrix (Fin n) (Fin n) ℚ) (B : ι → Matrix (Fin m) (Fin m) ℚ)
    (L : Matrix (Fin m) (Fin n) ℚ) (h : ∀ i, L * A i = B i * L) (u : ι → ℝ)
    (x : State n) :
    (L.map (Rat.castHom ℝ)).mulVec ((NormedSpace.exp (realPencil A u)).mulVec x) =
      (NormedSpace.exp (realPencil B u)).mulVec ((L.map (Rat.castHom ℝ)).mulVec x) :=
  exp_mulVec_intertwining _ _ _ (realPencil_intertwining A B L h u) x

end
end PolynomialLift
end ContinuousBilinear
