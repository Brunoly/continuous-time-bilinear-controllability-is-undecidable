import ContinuousBilinear.FeedbackProof
import ContinuousBilinear.IntegrableBilinearSolutions
import ContinuousBilinear.IntervalStepControlDensity
import ContinuousBilinear.StepControlTransitions

namespace ContinuousBilinear.FeedbackData

open Set MeasureTheory Filter
open scoped Topology

variable {d m : ℕ}

/-- The closed orbit cone is invariant under integrable controls, by approximating
the controls by finite interval steps and passing to the limit in the trajectories. -/
theorem integralTrajectory_mem_nonnegativeOrbitCone_of_stepApproximation
    (F : FeedbackData d m) (hK : ∀ i j, Commute (F.K i) (F.K j)) (hn : ¬ F.HasNegativePairing)
    {T : ℝ} (_hT : 0 ≤ T) {u : ℝ → Fin (m + 1) → ℝ} (hu : IntegrableOn u (Icc 0 T))
    {z : ℝ → State (d + 1)} (hz : ContinuousOn z (Icc 0 T))
    (h0 : z 0 ∈ F.nonnegativeOrbitCone)
    (hEq : ∀ t ∈ Icc 0 T, z t = @Add.add (State (d + 1)) _ (z 0)
      (∫ s in (0 : ℝ)..t, (generator F.plant (u s) : RealMatrix (d + 1)).mulVec (z s))) :
    ∀ t ∈ Icc 0 T, z t ∈ F.nonnegativeOrbitCone := by
  classical
  intro t ht
  rcases ht.1.eq_or_lt with hzero | htpos
  · simpa only [← hzero] using h0
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  let ε (j : ℕ) : ℝ := 1 / (j + 1 : ℝ)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  choose n hpos a ha herr using fun j =>
    exists_intervalStepControl_integral_norm_sub_lt htpos (hε j) (hu.mono_set hsub)
  let h (j : ℕ) := t / (n j : ℝ)
  let v (j : ℕ) : ℝ → Fin (m + 1) → ℝ := intervalStepControl (h j) (a j)
  have hstep (j : ℕ) : 0 < h j := by
    have hn' : (0 : ℝ) < n j := by exact_mod_cast hpos j
    exact div_pos htpos hn'
  have htime (j : ℕ) : (n j : ℝ) * h j = t := by
    have hn' : (n j : ℝ) ≠ 0 := by exact_mod_cast (hpos j).ne'
    dsimp [h]
    field_simp
  have hlimit : Tendsto (fun j => ∫ s in (0 : ℝ)..t, ‖v j s - u s‖) atTop (𝓝 0) := by
    have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hεlim
    · exact fun _ => intervalIntegral.integral_nonneg_of_forall ht.1 (fun _ => norm_nonneg _)
    · intro j
      simpa only [v, h, norm_sub_rev] using (herr j).le
  obtain ⟨w, hw, hwEq, hwlim⟩ := exists_integralSolutions_tendsto_of_control_L1 F.plant
    ht.1 (hu.mono_set hsub) ha hlimit (hz.mono hsub) (fun s hs => hEq s (hsub hs))
  apply F.isClosed_nonnegativeOrbitCone.mem_of_tendsto (hwlim t ⟨ht.1, le_rfl⟩)
  apply Eventually.of_forall
  intro j
  have hw0 : w j 0 = z 0 := by
    have hzero := hwEq j 0 ⟨le_rfl, ht.1⟩
    rw [intervalIntegral.integral_same] at hzero
    change w j 0 = z 0 + (0 : State (d + 1)) at hzero
    exact hzero.trans (add_zero _)
  have hvj : IntegrableOn (v j) (Icc 0 ((n j : ℝ) * h j)) := by
    rw [htime]
    exact ha j
  have hwj : ContinuousOn (w j) (Icc 0 ((n j : ℝ) * h j)) := by
    rw [htime]
    exact hw j
  have heqj (s : ℝ) (hs : s ∈ Icc 0 ((n j : ℝ) * h j)) :
      w j s = w j 0 + ∫ r in (0 : ℝ)..s, (generator F.plant (v j r)).mulVec (w j r) := by
    rw [htime] at hs
    rw [hw0]
    exact hwEq j s hs
  obtain ⟨M, hM, hEnd⟩ := exists_transition_of_uniform_step F.plant (hstep j) (a j)
    (fun i _ hi => intervalStepControl_eq_on_Ico (hstep j) (a j) i hi) hvj hwj heqj
  rw [htime, hw0] at hEnd
  rw [← hEnd]
  exact F.transition_preserves_nonnegativeOrbitCone hK hn hM h0

/-- The invariant cone excludes global controllability when all orbit pairings
are nonnegative. -/
theorem hasNegativePairing_of_integrableControls
    (F : FeedbackData d m) (hK : ∀ i j, Commute (F.K i) (F.K j))
    (hc : GloballyControllableWithIntegrableControls F.plant) : F.HasNegativePairing := by
  by_contra hn
  let x : State (d + 1) := Fin.cases 1 0
  have hx : x ≠ 0 := fun heq => by
    have := congrFun heq 0
    norm_num [x] at this
  have hxC : x ∈ F.nonnegativeOrbitCone := by
    refine ⟨zero_le_one, fun t => ?_⟩
    have hz : (fun i : Fin d => x i.succ) = 0 := by funext i; rfl
    rw [hz, Matrix.mulVec_zero]
    simp [pairing]
  obtain ⟨T, u, z, hT, hu, hz, h0, hEnd, hEq⟩ := hc x (-x) hx (neg_ne_zero.mpr hx)
  have hCone := F.integralTrajectory_mem_nonnegativeOrbitCone_of_stepApproximation hK hn
    hT hu hz (h0.symm ▸ hxC) (fun t ht => by rw [h0]; exact hEq t ht) T ⟨hT, le_rfl⟩
  have hneg := hCone.1
  rw [hEnd] at hneg
  norm_num [x, Pi.neg_apply] at hneg

end ContinuousBilinear.FeedbackData
