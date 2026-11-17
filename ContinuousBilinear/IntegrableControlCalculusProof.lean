import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.ContDiff.RCLike

open Set MeasureTheory Filter
open scoped Interval

namespace ContinuousBilinear

/-- A Bochner primitive is absolutely continuous, by domination by the scalar
primitive of the norm. -/
theorem absolutelyContinuousOnInterval_primitive {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : ℝ → E} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    AbsolutelyContinuousOnInterval (fun t => ∫ s in a..t, f s) a b := by
  have hscalar := hf.norm.absolutelyContinuousOnInterval_intervalIntegral
    (c := a) (left_mem_uIcc)
  rw [absolutelyContinuousOnInterval_iff] at hscalar ⊢
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hscalar ε hε
  refine ⟨δ, hδ, fun E hE hlen => lt_of_le_of_lt ?_ (hbound E hE hlen)⟩
  apply Finset.sum_le_sum
  intro i hi
  have hi₁ := (hE.1 i hi).1
  have hi₂ := (hE.1 i hi).2
  have hsub (t : ℝ) (ht : t ∈ uIcc a b) : IntervalIntegrable f volume a t :=
    hf.mono_set (uIcc_subset_uIcc left_mem_uIcc ht)
  rw [dist_eq_norm, Real.dist_eq,
    intervalIntegral.integral_interval_sub_left (hsub _ hi₁) (hsub _ hi₂),
    intervalIntegral.integral_interval_sub_left (hsub _ hi₁).norm (hsub _ hi₂).norm]
  exact intervalIntegral.norm_integral_le_abs_integral_norm

/-- The scalar fundamental theorem for absolutely continuous paths using an
explicit derivative representative. -/
theorem intervalIntegral_eq_sub_of_absolutelyContinuous {f f' : ℝ → ℝ} {a b : ℝ}
    (h : AbsolutelyContinuousOnInterval f a b)
    (hd : ∀ᵐ t, t ∈ uIcc a b → HasDerivAt f (f' t) t) :
    (∫ t in a..b, f' t) = f b - f a := by
  rw [← h.integral_deriv_eq_sub]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hd] with t ht hun
  exact (ht (uIoc_subset_uIcc hun)).deriv.symm

/-- A differentiable map with continuous derivative on a neighborhood of a
compact part of a finite-dimensional space preserves absolute continuity there. -/
theorem absolutelyContinuousOnInterval_comp_contDiff
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ 1 f)
    {g : ℝ → E} {a b : ℝ} (hg : AbsolutelyContinuousOnInterval g a b) :
    AbsolutelyContinuousOnInterval (f ∘ g) a b := by
  obtain ⟨R, hR⟩ := (isCompact_uIcc.image_of_continuousOn hg.continuousOn).isBounded.subset_closedBall
    (0 : E)
  obtain ⟨K, hK⟩ := hf.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall (0 : E) R) (isCompact_closedBall (0 : E) R)
  exact hK.comp_absolutelyContinuousOnInterval
    (fun t ht => hR ⟨t, ht, rfl⟩) hg

/-- Applying an absolutely continuous operator to an absolutely continuous
vector gives an absolutely continuous path. -/
theorem absolutelyContinuousOnInterval_clm_apply
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {A : ℝ → E →L[ℝ] F} {x : ℝ → E} {a b : ℝ}
    (hA : AbsolutelyContinuousOnInterval A a b)
    (hx : AbsolutelyContinuousOnInterval x a b) :
    AbsolutelyContinuousOnInterval (fun t => A t (x t)) a b := by
  obtain ⟨C, hC⟩ := hA.exists_bound
  obtain ⟨D, hD⟩ := hx.exists_bound
  have hdist (s t : ℝ) (hs : s ∈ uIcc a b) (ht : t ∈ uIcc a b) :
      dist (A s (x s)) (A t (x t)) ≤ C * dist (x s) (x t) + D * dist (A s) (A t) := by
    calc
      _ ≤ dist (A s (x s)) (A s (x t)) + dist (A s (x t)) (A t (x t)) :=
        dist_triangle _ _ _
      _ ≤ C * dist (x s) (x t) + D * dist (A s) (A t) := by
        apply add_le_add
        · rw [dist_eq_norm, dist_eq_norm, ← (A s).map_sub]
          exact ((A s).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right (hC s hs) (norm_nonneg _))
        · rw [dist_eq_norm, dist_eq_norm, ← ContinuousLinearMap.sub_apply, mul_comm D]
          exact ((A s - A t).le_opNorm _).trans
            (mul_le_mul_of_nonneg_left (hD t ht) (norm_nonneg _))
  unfold AbsolutelyContinuousOnInterval at hA hx ⊢
  have hsum := (hx.const_mul C).add (hA.const_mul D)
  apply squeeze_zero' ?_ ?_ (by simpa using hsum)
  · exact .of_forall (fun _ => Finset.sum_nonneg fun _ _ => dist_nonneg)
  rw [eventually_inf_principal]
  filter_upwards with (n, I) hI
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i hi =>
    hdist _ _ (hI.1 i hi).1 (hI.1 i hi).2

end ContinuousBilinear



