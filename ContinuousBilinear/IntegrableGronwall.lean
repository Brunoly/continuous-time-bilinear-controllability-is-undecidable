import ContinuousBilinear.IntegrableControlCalculusProof
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ContinuousBilinear

open Set MeasureTheory Filter
open scoped Interval

set_option maxHeartbeats 600000 in
/-- Gronwall's integral inequality with a nonnegative integrable coefficient. -/
theorem le_mul_exp_integral_of_le_add_integral {a b C : ℝ} {f k : ℝ → ℝ}
    (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    (hk : IntegrableOn k (Icc a b)) (hK : ∀ t ∈ Icc a b, 0 ≤ k t)
    (hbound : ∀ t ∈ Icc a b, f t ≤ C + ∫ s in a..t, k s * f s)
    {t : ℝ} (ht : t ∈ Icc a b) :
    f t ≤ C * Real.exp (∫ s in a..t, k s) := by
  have hkI := (intervalIntegrable_iff_integrableOn_Icc_of_le hab (by finiteness)).2 hk
  have hfkI := (intervalIntegrable_iff_integrableOn_Icc_of_le hab (by finiteness)).2
    (hk.mul_continuousOn hf isCompact_Icc)
  let K (u : ℝ) := ∫ s in a..u, k s
  let J (u : ℝ) := ∫ s in a..u, k s * f s
  let F (u : ℝ) := Real.exp (-K u) * (C + J u)
  let F' (u : ℝ) := Real.exp (-K u) * k u * (f u - (C + J u))
  have hAC : AbsolutelyContinuousOnInterval F a t := by
    have hK' : IntervalIntegrable k volume a t := hkI.mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le hab]
      exact Icc_subset_Icc_right ht.2)
    have hJ' : IntervalIntegrable (fun s => k s * f s) volume a t := hfkI.mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le hab]
      exact Icc_subset_Icc_right ht.2)
    have hExp : AbsolutelyContinuousOnInterval (fun u => Real.exp (-K u)) a t :=
      absolutelyContinuousOnInterval_comp_contDiff Real.contDiff_exp
        (absolutelyContinuousOnInterval_primitive hK').neg
    have hAdd : AbsolutelyContinuousOnInterval (fun u => C + J u) a t :=
      (isometry_add_left C).lipschitzWith.comp_absolutelyContinuousOnInterval
        (absolutelyContinuousOnInterval_primitive hJ')
    exact hExp.mul hAdd
  have hD : ∀ᵐ u, u ∈ uIcc a t → HasDerivAt F (F' u) u := by
    filter_upwards [hkI.ae_hasDerivAt_integral, hfkI.ae_hasDerivAt_integral] with u huK huJ hu
    have hu' : u ∈ uIcc a b := by
      rw [uIcc_of_le ht.1] at hu
      rw [uIcc_of_le hab]
      exact Icc_subset_Icc_right ht.2 hu
    have hKd : HasDerivAt K (k u) u := huK hu' a left_mem_uIcc
    have hJd : HasDerivAt J (k u * f u) u := huJ hu' a left_mem_uIcc
    convert (hKd.neg.exp.mul (hJd.const_add C)) using 1
    dsimp [F, F']
    ring
  have hSign : 0 ≤ᵐ[volume.restrict (Icc a t)] fun u => -F' u := by
    apply (ae_restrict_iff' measurableSet_Icc).2
    exact Eventually.of_forall fun u hu => by
      have hmem := Icc_subset_Icc_right ht.2 hu
      have hle : f u - (C + J u) ≤ 0 := sub_nonpos.mpr (hbound u hmem)
      exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg (Real.exp_nonneg _) (hK u hmem)) hle)
  have hInt := intervalIntegral.integral_nonneg_of_ae_restrict ht.1 hSign
  rw [intervalIntegral.integral_neg, intervalIntegral_eq_sub_of_absolutelyContinuous hAC hD]
    at hInt
  have hF : F t ≤ C := by
    have hFa : F a = C := by simp [F, J, K]
    linarith
  have hMajorant : C + J t ≤ C * Real.exp (K t) := by
    have hp := mul_le_mul_of_nonneg_left hF (Real.exp_nonneg (K t))
    change Real.exp (K t) * (Real.exp (-K t) * (C + J t)) ≤ _ at hp
    rwa [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul, mul_comm] at hp
  exact (hbound t ht).trans hMajorant

end ContinuousBilinear
