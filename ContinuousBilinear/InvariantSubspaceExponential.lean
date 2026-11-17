import ContinuousBilinear.ODEProof

open scoped Matrix.Norms.Operator
open Filter

namespace ContinuousBilinear

/-- An invariant finite-dimensional real subspace is preserved by the matrix
exponential. -/
theorem exp_mulVec_mem_of_mulVec_mem {n : ℕ} (A : RealMatrix n)
    (W : Submodule ℝ (State n)) (hA : ∀ x ∈ W, A.mulVec x ∈ W)
    {x : State n} (hx : x ∈ W) :
    (NormedSpace.exp A).mulVec x ∈ W := by
  let act : RealMatrix n →L[ℝ] State n := LinearMap.toContinuousLinearMap
    { toFun := fun M => M.mulVec x
      map_add' := fun M N => Matrix.add_mulVec M N x
      map_smul' := fun r M => Matrix.smul_mulVec r M x }
  have hpow (k : ℕ) : (A ^ k).mulVec x ∈ W := by
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      exact hA _ ih
  have hs := (NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) A).mapL act
  apply W.closed_of_finiteDimensional.mem_of_tendsto hs
  exact Eventually.of_forall fun s => W.sum_mem fun k _ => by
    change (((Nat.factorial k : ℝ)⁻¹) • A ^ k).mulVec x ∈ W
    rw [Matrix.smul_mulVec]
    exact W.smul_mem _ (hpow k)

end ContinuousBilinear
