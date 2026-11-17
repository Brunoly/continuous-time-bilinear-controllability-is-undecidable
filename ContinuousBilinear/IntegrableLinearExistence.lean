import ContinuousBilinear.IntegrableControlCalculusProof
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Topology.Order.ProjIcc

open Set MeasureTheory Filter
open scoped Interval NNReal

namespace ContinuousBilinear

private theorem exponential_primitive_integral {a b : ℝ} {k : ℝ → ℝ}
    (hk : IntervalIntegrable k volume a b) :
    (∫ s in a..b, k s * Real.exp (2 * ∫ r in a..s, k r)) =
      (Real.exp (2 * ∫ r in a..b, k r) - 1) / 2 := by
  let p (s : ℝ) := ∫ r in a..s, k r
  let f (s : ℝ) := Real.exp (2 * p s)
  have hp : AbsolutelyContinuousOnInterval p a b :=
    absolutelyContinuousOnInterval_primitive hk
  have hfp : ContDiff ℝ 1 (fun r : ℝ => Real.exp (2 * r)) :=
    Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)
  have hf : AbsolutelyContinuousOnInterval f a b :=
    absolutelyContinuousOnInterval_comp_contDiff hfp hp
  have hDeriv : ∀ᵐ s, s ∈ uIcc a b →
      HasDerivAt f (2 * (k s * Real.exp (2 * p s))) s := by
    filter_upwards [hk.ae_hasDerivAt_integral] with s hs hsI
    have hp' : HasDerivAt p (k s) s := hs hsI a left_mem_uIcc
    have hf' : HasDerivAt f (Real.exp (2 * p s) * (2 * k s)) s := by
      simpa only [f, Function.comp_def] using
        (Real.hasDerivAt_exp (2 * p s)).comp s (hp'.const_mul 2)
    convert hf' using 1
    ring
  have hFTC := intervalIntegral_eq_sub_of_absolutelyContinuous hf hDeriv
  rw [intervalIntegral.integral_const_mul] at hFTC
  have ha : f a = 1 := by simp [f, p]
  rw [ha] at hFTC
  change (∫ s in a..b, k s * Real.exp (2 * p s)) = (f b - 1) / 2
  linarith

private theorem intervalIntegrable_subinterval {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {a b t : ℝ} (ht : t ∈ Icc a b) (hf : IntegrableOn f (Icc a b)) :
    IntervalIntegrable f volume a t :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1 (by finiteness)).mpr
    (hf.mono_set (Icc_subset_Icc_right ht.2))

set_option maxHeartbeats 400000 in
/-- A linear integral equation with integrable Banach-algebra coefficient
has a continuous solution for every initial value on a compact interval.
The exponentially weighted continuous-path norm gives a contraction on
the entire interval. -/
theorem exists_continuousOn_of_integrable_linear_equation
    {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    {a b : ℝ} (hab : a ≤ b) {M : ℝ → A} (hM : IntegrableOn M (Icc a b)) (x₀ : A) :
    ∃ X : ℝ → A, ContinuousOn X (Icc a b) ∧
      ∀ t ∈ Icc a b, X t = x₀ + ∫ s in a..t, M s * X s := by
  let I := Icc a b
  let _ : CompactSpace I := isCompact_iff_compactSpace.mp isCompact_Icc
  let k (s : ℝ) := ‖M s‖
  let p (t : ℝ) := ∫ s in a..t, k s
  let V (t : ℝ) := Real.exp (2 * p t)
  let W (t : ℝ) := Real.exp (-(2 * p t))
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hk : IntegrableOn k (Icc a b) := hM.norm
  have hp : ContinuousOn p (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      (absolutelyContinuousOnInterval_primitive (intervalIntegrable_subinterval hb hk)).continuousOn
  have hpV : ContinuousOn V (Icc a b) := Real.continuous_exp.comp_continuousOn (hp.const_mul 2)
  have hpW : ContinuousOn W (Icc a b) := Real.continuous_exp.comp_continuousOn (hp.const_mul 2).neg
  have hVW (t : ℝ) : V t * W t = 1 := by simp [V, W, Real.exp_neg, Real.exp_ne_zero]
  let path (X : C(I, A)) (t : ℝ) : A := V t • X (projIcc a b hab t)
  have hPath (X : C(I, A)) : ContinuousOn (path X) (Icc a b) :=
    hpV.smul (X.continuous.comp continuous_projIcc).continuousOn
  have hCoeff (X : C(I, A)) : IntegrableOn (fun s => M s * path X s) (Icc a b) :=
    hM.mul_continuousOn (hPath X) isCompact_Icc
  let integral (X : C(I, A)) (t : ℝ) := ∫ s in a..t, M s * path X s
  have hIntegral (X : C(I, A)) : ContinuousOn (integral X) (Icc a b) := by
    simpa only [uIcc_of_le hab] using
      (absolutelyContinuousOnInterval_primitive (intervalIntegrable_subinterval hb (hCoeff X))).continuousOn
  let picard (X : C(I, A)) : C(I, A) :=
    ⟨fun t => W t • (x₀ + integral X t),
      continuousOn_iff_continuous_domRestrict.mp
        (hpW.smul (continuousOn_const.add (hIntegral X)))⟩
  have contract : ContractingWith (1 / 2 : ℝ≥0) picard := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul (fun X Y => ?_)⟩
    apply (ContinuousMap.dist_le (by positivity)).mpr
    intro t
    have ht : (t : ℝ) ∈ Icc a b := t.property
    let f (s : ℝ) := M s * path X s - M s * path Y s
    let c := dist X Y
    have hc : 0 ≤ c := dist_nonneg
    have hDiff (s : ℝ) :
        f s = V s • (M s * (X (projIcc a b hab s) - Y (projIcc a b hab s))) := by
      simp [f, path, smul_sub, mul_sub]
    have hNorm (s : ℝ) : ‖f s‖ ≤ c * (k s * V s) := by
      rw [hDiff, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
      have hdist :
          ‖X (projIcc a b hab s) - Y (projIcc a b hab s)‖ ≤ c := by
        rw [← dist_eq_norm]
        exact (ContinuousMap.dist_le hc).mp le_rfl _
      calc
        _ ≤ V s * (k s * ‖X (projIcc a b hab s) - Y (projIcc a b hab s)‖) :=
          mul_le_mul_of_nonneg_left (norm_mul_le _ _) (Real.exp_pos _).le
        _ ≤ V s * (k s * c) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdist (norm_nonneg _))
            (Real.exp_pos _).le
        _ = c * (k s * V s) := by ring
    have hIntBound : IntervalIntegrable (fun s => c * (k s * V s)) volume a t :=
      intervalIntegrable_subinterval ht ((hk.mul_continuousOn hpV isCompact_Icc).const_mul c)
    have hDiffInt : ‖∫ s in a..t, f s‖ ≤ c * ((V t - 1) / 2) := by
      have hle := intervalIntegral.norm_integral_le_of_norm_le ht.1
        (ae_of_all volume fun s _ => hNorm s) hIntBound
      rwa [intervalIntegral.integral_const_mul, exponential_primitive_integral (intervalIntegrable_subinterval ht hk)] at hle
    have hW : 0 ≤ W t := (Real.exp_pos _).le
    have hdist : dist (picard X t) (picard Y t) = W t * ‖∫ s in a..t, f s‖ := by
      change dist (W t • (x₀ + integral X t)) (W t • (x₀ + integral Y t)) = _
      rw [dist_eq_norm, ← smul_sub, norm_smul, Real.norm_of_nonneg hW]
      congr 1
      have he : (x₀ + integral X t) - (x₀ + integral Y t) = integral X t - integral Y t := by abel
      rw [he]
      exact congrArg norm
        (intervalIntegral.integral_sub (intervalIntegrable_subinterval ht (hCoeff X)) (intervalIntegrable_subinterval ht (hCoeff Y))).symm
    rw [hdist]
    calc
      _ ≤ W t * (c * ((V t - 1) / 2)) := mul_le_mul_of_nonneg_left hDiffInt hW
      _ = c * ((V t * W t - W t) / 2) := by ring
      _ ≤ (1 / 2 : ℝ) * c := by rw [hVW]; nlinarith
      _ = _ := by norm_num [c]
  let X := ContractingWith.fixedPoint picard contract
  have hFixed : picard X = X := contract.fixedPoint_isFixedPt
  refine ⟨path X, hPath X, fun t ht => ?_⟩
  have hEval := congrArg (fun Y : C(I, A) => Y ⟨t, ht⟩) hFixed
  have he : W t • (x₀ + integral X t) = X ⟨t, ht⟩ := hEval
  change V t • X (projIcc a b hab t) = x₀ + integral X t
  rw [projIcc_of_mem hab ht, ← he, smul_smul, hVW, one_smul]

end ContinuousBilinear


