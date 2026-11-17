import ContinuousBilinear.FeedbackFastControlProof
import ContinuousBilinear.FeedbackShearMatrixProof
import ContinuousBilinear.FeedbackShearAlgebraProof

namespace ContinuousBilinear.FeedbackData

open Filter NormedSpace
open scoped Topology Matrix.Norms.Operator

variable {d m : ℕ}

private theorem exp_eq_one_add_of_sq_eq_zero (M : RealMatrix (d + 1)) (hM : M * M = 0) :
    exp M = 1 + M := by
  simp only [NormedSpace.exp_eq_tsum_rat]
  rw [tsum_eq_sum (s := Finset.range 2)]
  · norm_num [Finset.sum_range_succ]
  · intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt (Finset.mem_range.not.mp hn))
    simp [pow_add, pow_two, hM]

private theorem drift_eq_vecMulVec (F : FeedbackData d m) :
    (F.plant.drift : RealMatrix (d + 1)) =
      (1 / 2 : ℝ) • Matrix.vecMulVec (Fin.cases 1 F.b) (Fin.cases 1 F.ell) := by
  ext i j
  change ((1 / 2 : ℝ) * Fin.cases 1 F.b i) * Fin.cases 1 F.ell j =
    (1 / 2 : ℝ) * (Fin.cases 1 F.b i * Fin.cases 1 F.ell j)
  ring

private theorem scalarBlock_smul_one_vecMul (c s : ℝ) (z : State d) :
    Matrix.vecMul (Fin.cases s z) (scalarBlock d (1, c • (1 : RealMatrix d))) =
      Fin.cases s (c • z) := by
  funext j
  refine Fin.cases ?_ (fun b => ?_) j
  · simp [scalarBlock, RingHom.coe_mk, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  · simp [scalarBlock, RingHom.coe_mk, Matrix.vecMul, dotProduct, Fin.sum_univ_succ,
      Matrix.one_apply, mul_ite, eq_comm, mul_comm]

private theorem scalarBlock_smul_one_mulVec (c s : ℝ) (z : State d) :
    (scalarBlock d (1, c • (1 : RealMatrix d))).mulVec (Fin.cases s z) =
      Fin.cases s (c • z) := by
  rw [scalarBlock_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  simp

private noncomputable def scalarBlockUnit (c : ℝ) (hc : c ≠ 0) : (RealMatrix (d + 1))ˣ where
  val := scalarBlock d (1, c • 1)
  inv := scalarBlock d (1, c⁻¹ • 1)
  val_inv := by
    rw [← map_mul, ← (scalarBlock d).map_one]
    congr 1
    simp [smul_smul, hc]
  inv_val := by
    rw [← map_mul, ← (scalarBlock d).map_one]
    congr 1
    simp [smul_smul, hc]

private theorem scaled_drift_mem (F : FeedbackData d m)
    {a : ℝ} (ha : 0 ≤ a) :
    exp (a • (F.plant.drift : RealMatrix (d + 1))) ∈ transitionMonoid F.plant := by
  have h := segmentTransition_mem F.plant a 0 ha
  simpa [segmentTransition, generator] using h

private theorem continuous_fin_cases (s : ℝ → ℝ) (z : ℝ → State d)
    (hs : Continuous s) (hz : Continuous z) :
    Continuous (fun r => @Fin.cases d (fun _ => ℝ) (s r) (z r)) := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hs
  · exact (continuous_apply j).comp hz

private theorem continuous_vecMulVec {s z : ℝ → State (d + 1)}
    (hs : Continuous s) (hz : Continuous z) :
    Continuous (fun r => Matrix.vecMulVec (s r) (z r)) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact ((continuous_apply i).comp hs).mul ((continuous_apply j).comp hz)

private theorem conjugate_scaled_drift (F : FeedbackData d m) (a c : ℝ) (hc : c ≠ 0) :
    (↑(scalarBlockUnit (d := d) c hc) : RealMatrix (d + 1)) *
        (@SMul.smul ℝ (RealMatrix (d + 1)) _ a F.plant.drift) *
        ↑((scalarBlockUnit (d := d) c hc)⁻¹) =
      (a / 2) • Matrix.vecMulVec (Fin.cases 1 (c • F.b)) (Fin.cases 1 (c⁻¹ • F.ell)) := by
  let X : RealMatrix (d + 1) :=
    Matrix.vecMulVec (Fin.cases 1 F.b) (Fin.cases 1 F.ell)
  let V : RealMatrix (d + 1) := ↑(scalarBlockUnit (d := d) c hc)
  let W : RealMatrix (d + 1) := ↑((scalarBlockUnit (d := d) c hc)⁻¹)
  rw [drift_eq_vecMulVec]
  change V * (a • ((1 / 2 : ℝ) • X)) * W = _
  rw [smul_smul, mul_smul_comm, smul_mul_assoc]
  rw [show a * (1 / 2 : ℝ) = a / 2 by ring]
  congr 1
  dsimp only [V, X, W]
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
  change Matrix.vecMulVec
    ((scalarBlock d (1, c • (1 : RealMatrix d))).mulVec (Fin.cases 1 F.b))
    (Matrix.vecMul (Fin.cases 1 F.ell) (scalarBlock d (1, c⁻¹ • (1 : RealMatrix d)))) = _
  rw [scalarBlock_smul_one_mulVec, scalarBlock_smul_one_vecMul]

/-- Nonnegative shears from the scalar axis into the state space arise as limits
of conjugated short drift intervals. -/
theorem nonnegativeShearToState_mem_topologicalClosure (F : FeedbackData d m)
    {t : ℝ} (ht : 0 ≤ t) :
    1 + t • shearToState F.b ∈ (transitionMonoid F.plant).topologicalClosure := by
  let S : Submonoid (RealMatrix (d + 1)) := (transitionMonoid F.plant).topologicalClosure
  let path : ℝ → RealMatrix (d + 1) := fun r =>
    t • Matrix.vecMulVec (Fin.cases r F.b) (Fin.cases 1 (r • F.ell))
  have hPath : Continuous path := (continuous_vecMulVec
    (continuous_fin_cases _ _ continuous_id continuous_const)
    (continuous_fin_cases _ _ continuous_const (continuous_id.smul continuous_const))).const_smul t
  have hl : Tendsto (fun r => exp (path r)) (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝 (exp (path 0))) := (exp_continuous.comp hPath).continuousWithinAt
  have hm (r : ℝ) (hr : 0 < r) : exp (path r) ∈ S := by
    let U := scalarBlockUnit (d := d) r⁻¹ (inv_ne_zero hr.ne')
    have heq : (↑U : RealMatrix (d + 1)) *
        (@SMul.smul ℝ (RealMatrix (d + 1)) _ (2 * t * r) F.plant.drift) *
        (↑U⁻¹ : RealMatrix (d + 1)) = path r := by
      rw [conjugate_scaled_drift F _ _ (inv_ne_zero hr.ne'), inv_inv]
      have hv : r • (@Fin.cases d (fun _ => ℝ) 1 (r⁻¹ • F.b)) =
          @Fin.cases d (fun _ => ℝ) r F.b := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp
        · simp [mul_inv_cancel_left₀ (by positivity : r ≠ 0)]
      have hscalar : (2 * t * r) / 2 = t * r := by ring
      dsimp only [path]
      rw [hscalar, ← smul_smul, ← Matrix.smul_vecMulVec, hv]
    rw [← heq, Matrix.exp_units_conj]
    apply S.mul_mem
    · apply S.mul_mem
      · exact F.scalarBlock_pos_smul_mem_topologicalClosure (inv_pos.mpr hr)
      · exact (transitionMonoid F.plant).le_topologicalClosure (F.scaled_drift_mem (by positivity))
    · change scalarBlock d (1, (r⁻¹)⁻¹ • 1) ∈ S
      rw [inv_inv]
      exact F.scalarBlock_pos_smul_mem_topologicalClosure hr
  have hlim := (transitionMonoid F.plant).isClosed_topologicalClosure.mem_of_tendsto hl
    (mem_of_superset self_mem_nhdsWithin fun r hr => hm r hr)
  have h0 : path 0 = t • shearToState F.b := by simp [path, shearToState]
  rw [h0, exp_eq_one_add_of_sq_eq_zero] at hlim
  · exact hlim
  · simp [shearToState_sq]

/-- Nonnegative shears from the state space into the scalar axis arise by
scaling in the opposite direction. -/
theorem nonnegativeShearToScalar_mem_topologicalClosure (F : FeedbackData d m)
    {t : ℝ} (ht : 0 ≤ t) :
    1 + t • shearToScalar F.ell ∈ (transitionMonoid F.plant).topologicalClosure := by
  let S : Submonoid (RealMatrix (d + 1)) := (transitionMonoid F.plant).topologicalClosure
  let path : ℝ → RealMatrix (d + 1) := fun r =>
    t • Matrix.vecMulVec (Fin.cases 1 (r • F.b)) (Fin.cases r F.ell)
  have hPath : Continuous path := (continuous_vecMulVec
    (continuous_fin_cases _ _ continuous_const (continuous_id.smul continuous_const))
    (continuous_fin_cases _ _ continuous_id continuous_const)).const_smul t
  have hl : Tendsto (fun r => exp (path r)) (𝓝[Set.Ioi (0 : ℝ)] 0)
      (𝓝 (exp (path 0))) := (exp_continuous.comp hPath).continuousWithinAt
  have hm (r : ℝ) (hr : 0 < r) : exp (path r) ∈ S := by
    let U := scalarBlockUnit (d := d) r hr.ne'
    have heq : (↑U : RealMatrix (d + 1)) *
        (@SMul.smul ℝ (RealMatrix (d + 1)) _ (2 * t * r) F.plant.drift) *
        (↑U⁻¹ : RealMatrix (d + 1)) = path r := by
      rw [conjugate_scaled_drift F _ _ hr.ne']
      have hv : r • (@Fin.cases d (fun _ => ℝ) 1 (r⁻¹ • F.ell)) =
          @Fin.cases d (fun _ => ℝ) r F.ell := by
        funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp
        · simp [mul_inv_cancel_left₀ (by positivity : r ≠ 0)]
      have hscalar : (2 * t * r) / 2 = t * r := by ring
      dsimp only [path]
      rw [hscalar, ← smul_smul, ← Matrix.vecMulVec_smul, hv]
    rw [← heq, Matrix.exp_units_conj]
    apply S.mul_mem
    · apply S.mul_mem
      · exact F.scalarBlock_pos_smul_mem_topologicalClosure hr
      · exact (transitionMonoid F.plant).le_topologicalClosure (F.scaled_drift_mem (by positivity))
    · exact F.scalarBlock_pos_smul_mem_topologicalClosure (inv_pos.mpr hr)
  have hlim := (transitionMonoid F.plant).isClosed_topologicalClosure.mem_of_tendsto hl
    (mem_of_superset self_mem_nhdsWithin fun r hr => hm r hr)
  have h0 : path 0 = t • shearToScalar F.ell := by simp [path, shearToScalar]
  rw [h0, exp_eq_one_add_of_sq_eq_zero] at hlim
  · exact hlim
  · simp [shearToScalar_sq]

end ContinuousBilinear.FeedbackData
