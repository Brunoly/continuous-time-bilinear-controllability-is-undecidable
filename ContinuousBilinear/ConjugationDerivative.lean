import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope

open Filter Set Topology

namespace ContinuousBilinear

theorem hasDerivAt_exp_conjugation_zero {R : Type*}
    [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R] (A X : R) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • A) * X * NormedSpace.exp (t • -A))
      (A * X - X * A) 0 := by
  have h₁ : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • A)) A 0 := by
    simpa using hasDerivAt_exp_smul_const A (0 : ℝ)
  have h₂ : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • -A)) (-A) 0 := by
    simpa using hasDerivAt_exp_smul_const (-A) (0 : ℝ)
  change HasDerivAt ((fun t : ℝ => NormedSpace.exp (t • A) * X) *
    (fun t : ℝ => NormedSpace.exp (t • -A))) (A * X - X * A) 0
  simpa [sub_eq_add_neg, add_comm] using (h₁.mul_const X).mul h₂

/-- A closed subspace invariant under conjugation by a positive-time flow
is invariant under the commutator with the generator. -/
theorem commutator_mem_of_exp_conjugation_mem {R : Type*}
    [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]
    (A : R) (L : Submodule ℝ R) (hClosed : IsClosed (L : Set R))
    (h : ∀ (t : ℝ), 0 < t → ∀ X ∈ L,
      NormedSpace.exp (t • A) * X * NormedSpace.exp (t • -A) ∈ L)
    {X : R} (hX : X ∈ L) : A * X - X * A ∈ L := by
  let f (t : ℝ) := NormedSpace.exp (t • A) * X * NormedSpace.exp (t • -A)
  have h0 : f 0 = X := by simp [f]
  have hd := (hasDerivAt_exp_conjugation_zero A X).tendsto_slope_zero_right
  change Tendsto (fun t : ℝ => t⁻¹ • (f (0 + t) - f 0)) (𝓝[>] 0)
    (𝓝 (A * X - X * A)) at hd
  apply hClosed.mem_of_tendsto hd
  filter_upwards [self_mem_nhdsWithin (s := Ioi (0 : ℝ))] with t ht
  rw [zero_add, h0]
  exact L.smul_mem _ (L.sub_mem (h t ht X hX) hX)

end ContinuousBilinear
