import ContinuousBilinear.TransitionProducts
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Module.FiniteDimension

open scoped Matrix.Norms.Operator

namespace ContinuousBilinear

private noncomputable def matrixActionAt {n : ℕ} (x : State n) :
    RealMatrix n →L[ℝ] State n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A.mulVec x
      map_add' := fun A B => Matrix.add_mulVec A B x
      map_smul' := fun t A => Matrix.smul_mulVec t A x }

theorem hasDerivAt_exp_mulVec {n : ℕ} (A : RealMatrix n) (x : State n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • A)).mulVec x)
      (A.mulVec ((NormedSpace.exp (t • A)).mulVec x)) t := by
  have h := (matrixActionAt x).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_exp_smul_const' A t)
  change HasDerivAt _ ((A * NormedSpace.exp (t • A)).mulVec x) t at h
  rwa [← Matrix.mulVec_mulVec] at h

/-- The matrix exponential gives the unique solution on a nonnegative time interval. -/
theorem eqOn_exp_mulVec_of_hasDerivWithinAt {n : ℕ} (A : RealMatrix n)
    (x : State n) (z : ℝ → State n) (T : ℝ) (h0 : z 0 = x)
    (hDeriv : ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt z (A.mulVec (z t)) (Set.Icc 0 T) t) :
    Set.EqOn z (fun t => (NormedSpace.exp (t • A)).mulVec x) (Set.Icc 0 T) := by
  let v : State n →L[ℝ] State n := LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)
  let w (t : ℝ) := (NormedSpace.exp (t • A)).mulVec x
  have hw (t : ℝ) : HasDerivAt w (v (w t)) t := hasDerivAt_exp_mulVec A x t
  have hz (t : ℝ) (ht : t ∈ Set.Ico 0 T) :
      HasDerivWithinAt z (v (z t)) (Set.Ici t) t := by
    have hInterval : Set.Icc t T ∈ nhdsWithin t (Set.Ici t) := Icc_mem_nhdsGE ht.2
    exact (hDeriv t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset hInterval (Set.Icc_subset_Icc_left ht.1))
  exact ODE_solution_unique_of_mem_Icc_right (s := fun _ => Set.univ)
    (fun _ _ => v.lipschitzWith.lipschitzOnWith)
    (fun t ht => (hDeriv t ht).continuousWithinAt) hz (fun _ _ => Set.mem_univ _)
    (fun t _ => (hw t).continuousAt.continuousWithinAt)
    (fun t _ => (hw t).hasDerivWithinAt) (fun _ _ => Set.mem_univ _)
    (by simpa [w, NormedSpace.exp_zero] using h0)

theorem constantControlSegment_iff (P : Plant ℝ) (x y : State P.dimension) :
    ConstantControlSegment P x y ↔
      ∃ (t : ℝ) (u : Fin P.controls → ℝ), 0 < t ∧
        Matrix.mulVec (segmentTransition P t u) x = y := by
  constructor
  · rintro ⟨T, u, z, hT, h0, hTz, hDeriv⟩
    have hEq := eqOn_exp_mulVec_of_hasDerivWithinAt (generator P u) x z T h0 hDeriv
    exact ⟨T, u, hT, (hEq ⟨hT.le, le_rfl⟩).symm.trans hTz⟩
  · rintro ⟨T, u, hT, rfl⟩
    refine ⟨T, u, fun t => (segmentTransition P t u).mulVec x, hT, ?_, rfl, ?_⟩
    · simp [segmentTransition, NormedSpace.exp_zero]
    · intro t _
      exact (hasDerivAt_exp_mulVec (generator P u) x t).hasDerivWithinAt

theorem differentialEquationSemantics : Targets.DifferentialEquationSemantics :=
  differentialEquationSemantics_of_constantControl constantControlSegment_iff

end ContinuousBilinear
