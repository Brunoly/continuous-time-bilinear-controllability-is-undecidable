import ContinuousBilinear.FeedbackConeProof
import ContinuousBilinear.TransitionProducts
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace ContinuousBilinear.FeedbackData

open Filter
open scoped Topology Matrix.Norms.Operator
open NormedSpace

variable {d m : ℕ}

theorem exp_controlGenerator_mem_topologicalClosure (F : FeedbackData d m)
    (u : Fin (m + 1) → ℝ) :
    exp (F.controlGenerator u) ∈ (transitionMonoid F.plant).topologicalClosure := by
  let A : RealMatrix (d + 1) := F.plant.drift
  let B : RealMatrix (d + 1) := F.controlGenerator u
  let r : ℕ → ℝ := fun n => (n + 1 : ℝ)⁻¹
  have hr : Tendsto r atTop (𝓝 0) := by
    simpa [r, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hpath : Tendsto (fun n => exp (r n • A + B)) atTop (𝓝 (exp B)) := by
    have hArg : Continuous (fun s : ℝ => s • A + B) := by fun_prop
    have hExp : Continuous (fun s : ℝ => exp (s • A + B)) :=
      exp_continuous.comp hArg
    simpa only [zero_smul, zero_add, Function.comp_def] using hExp.continuousAt.tendsto.comp hr
  apply (transitionMonoid F.plant).isClosed_topologicalClosure.mem_of_tendsto hpath
  apply Eventually.of_forall
  intro n
  refine (transitionMonoid F.plant).le_topologicalClosure ?_
  let u' : Fin (m + 1) → ℝ := (n + 1 : ℝ) • u
  have hn : 0 < (n + 1 : ℝ) := by positivity
  have hru : r n • u' = u := by
    rw [show u' = (n + 1 : ℝ) • u from rfl, smul_smul]
    simp [r, hn.ne']
  have hseg : (segmentTransition F.plant (r n) u' : RealMatrix (d + 1)) =
      exp (r n • A + B) := by
    have hg : (generator F.plant u' : RealMatrix (d + 1)) = A + F.controlGenerator u' :=
      F.generator_eq_drift_add_controlGenerator u'
    calc
      _ = exp (r n • (A + F.controlGenerator u')) :=
        congrArg (fun Q : RealMatrix (d + 1) => exp (r n • Q)) hg
      _ = _ := by rw [smul_add, F.smul_controlGenerator, hru]
  rw [← hseg]
  exact segmentTransition_mem _ _ _ (by dsimp [r]; positivity)

theorem scalarBlock_orbitMatrix_mem_topologicalClosure (F : FeedbackData d m)
    (t : Fin m → ℝ) :
    scalarBlock d (1, F.orbitMatrix t) ∈ (transitionMonoid F.plant).topologicalClosure := by
  simpa [F.exp_controlGenerator] using
    F.exp_controlGenerator_mem_topologicalClosure (Fin.cases 0 t)

theorem scalarBlock_pos_smul_mem_topologicalClosure (F : FeedbackData d m)
    {c : ℝ} (hc : 0 < c) :
    scalarBlock d (1, c • (1 : RealMatrix d)) ∈ (transitionMonoid F.plant).topologicalClosure := by
  have h0 : (fun _ : Fin m => (0 : ℝ)) = 0 := rfl
  simpa only [F.exp_controlGenerator, Fin.cases_zero, Fin.cases_succ, Pi.zero_apply, h0,
    orbitMatrix_zero, Real.exp_log hc] using
    F.exp_controlGenerator_mem_topologicalClosure (Fin.cases (Real.log c) 0)

end ContinuousBilinear.FeedbackData
