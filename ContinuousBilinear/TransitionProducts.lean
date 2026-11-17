import ContinuousBilinear.Targets
import ContinuousBilinear.MatrixExponentialDeterminant
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

namespace ContinuousBilinear

private theorem finiteTransition_foldl (P : Plant ℝ) (steps : List (Segment P.controls))
    (M : RealMatrix P.dimension) :
    steps.foldl (fun A s => segmentTransition P s.1 s.2 * A) M =
      finiteTransition P steps * M := by
  unfold finiteTransition
  rw [← List.foldl_hom (fun A : RealMatrix P.dimension => A * M)
    (g₁ := fun A s => segmentTransition P s.1 s.2 * A)
    (g₂ := fun A s => segmentTransition P s.1 s.2 * A)
    (l := steps) (init := 1) (fun A s => (mul_assoc _ _ _).symm)]
  simp

theorem finiteTransition_append (P : Plant ℝ) (first last : List (Segment P.controls)) :
    finiteTransition P (first ++ last) = finiteTransition P last * finiteTransition P first := by
  unfold finiteTransition
  rw [List.foldl_append]
  exact finiteTransition_foldl P last (finiteTransition P first)

theorem segmentTransition_mem (P : Plant ℝ) (t : ℝ) (u : Fin P.controls → ℝ)
    (ht : 0 ≤ t) : segmentTransition P t u ∈ transitionMonoid P :=
  Submonoid.subset_closure ⟨t, u, ht, rfl⟩

theorem transitionProductSemantics : Targets.TransitionProductSemantics := by
  intro P M
  constructor
  · intro hM
    change M ∈ Submonoid.closure _ at hM
    induction hM using Submonoid.closure_induction with
    | mem A h =>
      obtain ⟨t, u, ht, rfl⟩ := h
      rcases eq_or_lt_of_le ht with rfl | hp
      · exact ⟨[], by simp [PositiveDurations], by simp [finiteTransition, segmentTransition]⟩
      · exact ⟨[(t, u)], by simpa [PositiveDurations], by simp [finiteTransition]⟩
    | one => exact ⟨[], by simp [PositiveDurations], rfl⟩
    | mul A B _ _ hA hB =>
      obtain ⟨as, ha, rfl⟩ := hA
      obtain ⟨bs, hb, rfl⟩ := hB
      refine ⟨bs ++ as, ?_, finiteTransition_append P bs as⟩
      intro s hs
      rcases List.mem_append.mp hs with hs | hs
      · exact hb s hs
      · exact ha s hs
  · rintro ⟨steps, hsteps, rfl⟩
    induction steps with
    | nil => exact (transitionMonoid P).one_mem
    | cons s ss ih =>
      have hs := hsteps s (List.mem_cons_self)
      have hss : PositiveDurations ss := fun a ha => hsteps a (List.mem_cons_of_mem _ ha)
      change finiteTransition P ([s] ++ ss) ∈ transitionMonoid P
      rw [finiteTransition_append]
      exact (transitionMonoid P).mul_mem (ih hss) (by
        simpa [finiteTransition] using segmentTransition_mem P s.1 s.2 hs.le)

theorem det_exp_pos {n : ℕ} (A : RealMatrix n) : 0 < (NormedSpace.exp A).det := by
  have h := det_exp_smul A 1
  simp only [one_smul, one_mul] at h
  rw [h]
  exact Real.exp_pos _

theorem det_pos_of_mem_transitionMonoid (P : Plant ℝ) {M : RealMatrix P.dimension}
    (hM : M ∈ transitionMonoid P) : 0 < M.det := by
  change M ∈ Submonoid.closure _ at hM
  induction hM using Submonoid.closure_induction with
  | mem A h =>
    obtain ⟨t, u, _, rfl⟩ := h
    exact det_exp_pos _
  | one => simp
  | mul A B _ _ ha hb => simpa [Matrix.det_mul] using mul_pos ha hb


/-- Endpoint formulas for single constant-control intervals give the corresponding
formula for any finite concatenation. -/
theorem differentialEquationSemantics_of_constantControl
    (hSegment : ∀ (P : Plant ℝ) (x y : State P.dimension),
      ConstantControlSegment P x y ↔
        ∃ (t : ℝ) (u : Fin P.controls → ℝ), 0 < t ∧
          Matrix.mulVec (segmentTransition P t u) x = y) :
    Targets.DifferentialEquationSemantics := by
  intro P x y
  constructor
  · intro h
    change Relation.ReflTransGen (ConstantControlSegment P) x y at h
    induction h with
    | refl => exact ⟨1, (transitionMonoid P).one_mem, Matrix.one_mulVec _⟩
    | tail _ hStep ih =>
      obtain ⟨M, hM, hx⟩ := ih
      obtain ⟨t, u, ht, hy⟩ := (hSegment P _ _).mp hStep
      refine ⟨segmentTransition P t u * M,
        (transitionMonoid P).mul_mem (segmentTransition_mem P t u ht.le) hM, ?_⟩
      rwa [← Matrix.mulVec_mulVec, hx]
  · rintro ⟨M, hM, rfl⟩
    obtain ⟨steps, hsteps, rfl⟩ := (transitionProductSemantics P M).mp hM
    clear hM
    induction steps generalizing x with
    | nil =>
      simp only [finiteTransition, List.foldl_nil, Matrix.one_mulVec]
      exact Relation.ReflTransGen.refl
    | cons s ss ih =>
      have ht := hsteps s (List.mem_cons_self)
      have hss : PositiveDurations ss := fun a ha => hsteps a (List.mem_cons_of_mem _ ha)
      have hSingle := (hSegment P x _).mpr ⟨s.1, s.2, ht, rfl⟩
      change PiecewiseConstantReachable P x (Matrix.mulVec (finiteTransition P ([s] ++ ss)) x)
      rw [finiteTransition_append, ← Matrix.mulVec_mulVec]
      simpa [finiteTransition, PiecewiseConstantReachable] using
        (Relation.ReflTransGen.single hSingle).trans (ih _ hss)
end ContinuousBilinear
