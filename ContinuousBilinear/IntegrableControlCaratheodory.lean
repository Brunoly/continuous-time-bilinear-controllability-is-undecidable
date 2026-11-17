import ContinuousBilinear.IntegrableControlCalculusProof
import ContinuousBilinear.IntegrableControlProof

open Set MeasureTheory Filter
open scoped Interval

namespace ContinuousBilinear

/-- An integrable control satisfies the finite-horizon integral equation
exactly when its state is absolutely continuous and satisfies the bilinear
differential equation almost everywhere on the horizon. -/
theorem integralEquation_iff_absolutelyContinuous_and_ae_hasDerivAt
    (P : Plant ℝ) {T : ℝ} (hT : 0 ≤ T)
    {u : ℝ → Fin P.controls → ℝ} (hu : IntegrableOn u (Icc 0 T))
    {z : ℝ → State P.dimension} :
    (ContinuousOn z (Icc 0 T) ∧ ∀ t ∈ Icc 0 T,
      z t = z 0 + ∫ s in (0 : ℝ)..t, (generator P (u s)).mulVec (z s)) ↔
    (AbsolutelyContinuousOnInterval z 0 T ∧ ∀ᵐ t, t ∈ Icc 0 T →
      HasDerivAt z ((generator P (u t)).mulVec (z t)) t) := by
  let f (s : ℝ) := (generator P (u s)).mulVec (z s)
  have hfInt (hz : ContinuousOn z (Icc 0 T)) : IntegrableOn f (Icc 0 T) :=
    integrableOn_generator_mulVec P hu hz
  constructor
  · rintro ⟨hz, hEq⟩
    have hf := (intervalIntegrable_iff_integrableOn_Icc_of_le hT (by finiteness)).mpr (hfInt hz)
    constructor
    · have hAC := absolutelyContinuousOnInterval_primitive hf
      apply ((isometry_add_left (z 0)).lipschitzWith.comp_absolutelyContinuousOnInterval hAC).congr
      intro t ht
      exact (hEq t (by simpa only [uIcc_of_le hT] using ht)).symm
    · have hzero : ∀ᵐ t : ℝ, t ≠ 0 := by simp [ae_iff, measure_singleton]
      have hend : ∀ᵐ t : ℝ, t ≠ T := by simp [ae_iff, measure_singleton]
      filter_upwards [hf.ae_hasDerivAt_integral, hzero, hend] with t ht h₀ h₁ htI
      have htU : t ∈ uIcc 0 T := by simpa only [uIcc_of_le hT] using htI
      apply ((ht htU 0 left_mem_uIcc).const_add (z 0)).congr_of_eventuallyEq
      exact Filter.EventuallyEq.symm (Filter.mem_of_superset
        (Icc_mem_nhds (lt_of_le_of_ne htI.1 h₀.symm) (lt_of_le_of_ne htI.2 h₁))
        (fun s hs => (hEq s hs).symm))
  · rintro ⟨hAC, hderiv⟩
    have hz : ContinuousOn z (Icc 0 T) := by
      simpa only [uIcc_of_le hT] using hAC.continuousOn
    refine ⟨hz, fun t ht => ?_⟩
    have htU : t ∈ uIcc 0 T := by simpa only [uIcc_of_le hT] using ht
    have hsub : uIcc 0 t ⊆ uIcc 0 T := uIcc_subset_uIcc left_mem_uIcc htU
    have hfI := (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1 (by finiteness)).mpr
      ((hfInt hz).mono_set (Icc_subset_Icc_right ht.2))
    have hFTC : (∫ s in (0 : ℝ)..t, f s) = z t - z 0 := by
      ext i
      let L := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin P.dimension => ℝ) i
      change L (∫ s in (0 : ℝ)..t, f s) = L (z t) - L (z 0)
      rw [← L.intervalIntegral_comp_comm hfI]
      apply intervalIntegral_eq_sub_of_absolutelyContinuous
        (L.lipschitzWith.comp_absolutelyContinuousOnInterval (hAC.mono hsub))
      filter_upwards [hderiv] with s hs hsI
      exact L.hasFDerivAt.comp_hasDerivAt s
        (hs (by simpa only [uIcc_of_le hT] using hsub hsI))
    change z t = z 0 + ∫ s in (0 : ℝ)..t, f s
    rw [hFTC]
    abel

end ContinuousBilinear

