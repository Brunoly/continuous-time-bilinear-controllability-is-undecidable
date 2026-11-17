import ContinuousBilinear.FeedbackConeProof
import ContinuousBilinear.FeedbackTrotterProof

namespace ContinuousBilinear.FeedbackData

open Filter
open scoped Topology Matrix.Norms.Operator

variable {d m : ℕ}

/-- Matrices whose action preserves a given set of states. -/
private def preservingMatrices {n : ℕ} (C : Set (State n)) : Submonoid (RealMatrix n) where
  carrier := {A | ∀ ⦃x⦄, x ∈ C → A.mulVec x ∈ C}
  one_mem' := by simp
  mul_mem' := by
    intro A B hA hB x hx
    rw [← Matrix.mulVec_mulVec]
    exact hA (hB hx)

private theorem isClosed_preservingMatrices {n : ℕ} {C : Set (State n)} (hC : IsClosed C) :
    IsClosed ((preservingMatrices C : Submonoid (RealMatrix n)) : Set (RealMatrix n)) := by
  have h : ((preservingMatrices C : Submonoid (RealMatrix n)) : Set (RealMatrix n)) =
      ⋂ x : C, (fun A : RealMatrix n => A.mulVec x.val) ⁻¹' C := by
    ext A
    simp [preservingMatrices]
  rw [h]
  exact isClosed_iInter fun _ => hC.preimage (continuous_id.matrix_mulVec continuous_const)

/-- The exponential of the full generator preserves the cone in the absence
of a negative orbit pairing. -/
theorem segmentTransition_preserves_nonnegativeOrbitCone (F : FeedbackData d m)
    (hK : ∀ i j, Commute (F.K i) (F.K j)) (hn : ¬ F.HasNegativePairing)
    {t : ℝ} (ht : 0 ≤ t) (u : Fin (m + 1) → ℝ)
    {x : State (d + 1)} (hx : x ∈ F.nonnegativeOrbitCone) :
    (segmentTransition F.plant t u).mulVec x ∈ F.nonnegativeOrbitCone := by
  let D : RealMatrix (d + 1) := F.plant.drift
  let A : RealMatrix (d + 1) := t • D
  let B : RealMatrix (d + 1) := t • F.controlGenerator u
  let S := preservingMatrices F.nonnegativeOrbitCone
  let f : ℝ → RealMatrix (d + 1) := fun r => (1 + r • A) * NormedSpace.exp (r • B)
  have hLimit : Tendsto (fun n : ℕ => f ((n + 1 : ℝ)⁻¹) ^ (n + 1)) atTop
      (𝓝 (NormedSpace.exp (A + B))) := tendsto_split_euler A B
  have hstep {r : ℝ} (hr : 0 ≤ r) : f r ∈ S := by
    have h1 : 1 + r • A ∈ S := by
      intro y hy
      rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
      dsimp only [A]
      rw [Matrix.smul_mulVec]
      exact F.add_mem_nonnegativeOrbitCone hy
        (F.smul_mem_nonnegativeOrbitCone
          (F.smul_mem_nonnegativeOrbitCone (F.drift_preserves_nonnegativeOrbitCone hn hy) ht) hr)
    have h2 : NormedSpace.exp (r • B) ∈ S := by
      intro y hy
      change (NormedSpace.exp (r • (t • F.controlGenerator u))).mulVec y ∈ _
      rw [F.smul_controlGenerator, F.smul_controlGenerator]
      exact F.exp_controlGenerator_preserves_nonnegativeOrbitCone hK _ hy
    exact S.mul_mem h1 h2
  have hExp : NormedSpace.exp (A + B) ∈ S :=
    (isClosed_preservingMatrices (F.isClosed_nonnegativeOrbitCone)).mem_of_tendsto hLimit
      (Eventually.of_forall fun n => S.pow_mem (hstep (by positivity)) (n + 1))
  have heq : (segmentTransition F.plant t u : RealMatrix (d + 1)) = NormedSpace.exp (A + B) := by
    have hg : (generator F.plant u : RealMatrix (d + 1)) = D + F.controlGenerator u :=
      F.generator_eq_drift_add_controlGenerator u
    calc
      _ = NormedSpace.exp (t • (D + F.controlGenerator u)) :=
        congrArg (fun Q : RealMatrix (d + 1) => NormedSpace.exp (t • Q)) hg
      _ = _ := by rw [smul_add]
  rw [heq]
  exact hExp hx

theorem transition_preserves_nonnegativeOrbitCone (F : FeedbackData d m)
    (hK : ∀ i j, Commute (F.K i) (F.K j)) (hn : ¬ F.HasNegativePairing)
    {M : RealMatrix (d + 1)} (hM : M ∈ transitionMonoid F.plant)
    {x : State (d + 1)} (hx : x ∈ F.nonnegativeOrbitCone) :
    M.mulVec x ∈ F.nonnegativeOrbitCone := by
  have hSub : transitionMonoid F.plant ≤ preservingMatrices F.nonnegativeOrbitCone := by
    change Submonoid.closure ({M : RealMatrix (d + 1) |
      ∃ (t : ℝ) (u : Fin (m + 1) → ℝ), 0 ≤ t ∧
        M = (segmentTransition F.plant t u : RealMatrix (d + 1))}) ≤ _
    rw [Submonoid.closure_le]
    rintro _ ⟨t, u, ht, rfl⟩
    intro y hy
    exact F.segmentTransition_preserves_nonnegativeOrbitCone hK hn ht u hy
  exact (hSub hM) hx

/-- Necessity of a negative orbit pairing for global controllability. -/
theorem hasNegativePairing_of_globallyControllable (F : FeedbackData d m)
    (hK : ∀ i j, Commute (F.K i) (F.K j))
    (hc : GloballyControllable F.plant) : F.HasNegativePairing := by
  classical
  by_contra hn
  let x : State (d + 1) := Fin.cases 1 0
  have hx : x ≠ 0 := fun heq => by
    have := congrFun heq 0
    norm_num [x] at this
  have hnx : -x ≠ 0 := neg_ne_zero.mpr hx
  obtain ⟨M, hM, heq⟩ := hc x (-x) hx hnx
  have hxC : x ∈ F.nonnegativeOrbitCone := by
    refine ⟨zero_le_one, fun t => ?_⟩
    have hz : (fun i : Fin d => x i.succ) = 0 := by funext i; rfl
    rw [hz, Matrix.mulVec_zero]
    simp [pairing]
  have hnxC := F.transition_preserves_nonnegativeOrbitCone hK hn hM hxC
  have heq' : (M : RealMatrix (d + 1)).mulVec x = -x := heq
  have hnx' : -x ∈ F.nonnegativeOrbitCone :=
    Eq.mp (congrArg (fun y : State (d + 1) => y ∈ F.nonnegativeOrbitCone) heq') hnxC
  have hzero : 0 ≤ (-x) 0 := hnx'.1
  norm_num [x, Pi.neg_apply] at hzero

end ContinuousBilinear.FeedbackData
