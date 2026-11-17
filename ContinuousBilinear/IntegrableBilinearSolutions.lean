import ContinuousBilinear.IntegrableControlCaratheodory
import ContinuousBilinear.IntegrableLinearStability

namespace ContinuousBilinear

open Set MeasureTheory Filter
open scoped Topology

private noncomputable def matrixEndomorphism (n : ℕ) :
    RealMatrix n →ₗ[ℝ] (State n →L[ℝ] State n) where
  toFun M := M.mulVecLin.toContinuousLinearMap
  map_add' M N := by
    apply ContinuousLinearMap.ext
    intro x
    exact Matrix.add_mulVec M N x
  map_smul' c M := by
    apply ContinuousLinearMap.ext
    intro x
    exact Matrix.smul_mulVec c M x

set_option maxHeartbeats 700000 in
private theorem integrableOn_generatorEndomorphism (P : Plant ℝ)
    {a b : ℝ} {u : ℝ → Fin P.controls → ℝ} (hu : IntegrableOn u (Icc a b)) :
    IntegrableOn (fun s => matrixEndomorphism P.dimension (generator P (u s))) (Icc a b) := by
  let M := matrixEndomorphism P.dimension
  let A : Fin (P.controls + 1) → (State P.dimension →L[ℝ] State P.dimension) :=
    Fin.cases (M P.drift) (fun i => M (P.control i))
  let L : (Fin (P.controls + 1) → ℝ) →ₗ[ℝ] (State P.dimension →L[ℝ] State P.dimension) :=
    { toFun := fun v => ∑ i, v i • A i
      map_add' := fun v w => by simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c v => by simp [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum] }
  let v (t : ℝ) : Fin (P.controls + 1) → ℝ := Fin.cases 1 (u t)
  have hv : IntegrableOn v (Icc a b) := by
    apply Integrable.of_eval
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · change IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc a b)
      exact integrableOn_const (C := (1 : ℝ)) isCompact_Icc.measure_lt_top.ne
    · exact hu.eval j
  have hLv : IntegrableOn (fun t => L (v t)) (Icc a b) := by
    exact L.toContinuousLinearMap.integrable_comp hv
  have hEq (t : ℝ) : L (v t) = M (generator P (u t)) := by
    change (∑ i, v t i • A i) = M (generator P (u t))
    rw [Fin.sum_univ_succ, generator, M.map_add, map_sum]
    change (1 : ℝ) • M P.drift + (∑ i, u t i • M (P.control i)) = _
    simp only [one_smul, map_smul]
  simpa only [hEq] using hLv

private theorem exists_integralSolution (P : Plant ℝ) {T : ℝ}
    (hT : 0 ≤ T) {u : ℝ → Fin P.controls → ℝ} (hu : IntegrableOn u (Icc 0 T))
    (x : State P.dimension) :
    ∃ z : ℝ → State P.dimension, ContinuousOn z (Icc 0 T) ∧
      ∀ t ∈ Icc 0 T, z t = x + ∫ s in (0 : ℝ)..t, (generator P (u s)).mulVec (z s) := by
  let E := State P.dimension
  let A (s : ℝ) := matrixEndomorphism P.dimension (generator P (u s))
  have hA : IntegrableOn A (Icc 0 T) := integrableOn_generatorEndomorphism P hu
  obtain ⟨X, hX, hEq⟩ := exists_continuousOn_of_integrable_linear_equation hT hA
    (1 : E →L[ℝ] E)
  let L := ContinuousLinearMap.apply ℝ E x
  refine ⟨fun t => L (X t), L.continuous.comp_continuousOn hX, ?_⟩
  intro t ht
  have hInt : IntervalIntegrable (fun s => A s * X s) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1 (by finiteness)).mpr
      ((hA.mul_continuousOn hX isCompact_Icc).mono_set (Icc_subset_Icc_right ht.2))
  have h := congrArg L (hEq t ht)
  rw [L.map_add, ← L.intervalIntegral_comp_comm hInt] at h
  exact h

private theorem eqOn_of_integralSolutions (P : Plant ℝ) {T : ℝ}
    (hT : 0 ≤ T) {u : ℝ → Fin P.controls → ℝ} (hu : IntegrableOn u (Icc 0 T))
    {x : State P.dimension} {z w : ℝ → State P.dimension}
    (hz : ContinuousOn z (Icc 0 T)) (hw : ContinuousOn w (Icc 0 T))
    (hZ : ∀ t ∈ Icc 0 T, z t = x + ∫ s in (0 : ℝ)..t, (generator P (u s)).mulVec (z s))
    (hW : ∀ t ∈ Icc 0 T, w t = x + ∫ s in (0 : ℝ)..t, (generator P (u s)).mulVec (w s)) :
    EqOn z w (Icc 0 T) := by
  let A (s : ℝ) := matrixEndomorphism P.dimension (generator P (u s))
  have hA : IntegrableOn A (Icc 0 T) := integrableOn_generatorEndomorphism P hu
  have hAnorm : IntegrableOn (fun s => ‖A s‖) (Icc 0 T) := hA.norm
  have hBound (t : ℝ) (ht : t ∈ Icc 0 T) :
      ‖(z - w) t‖ ≤ 0 + ∫ s in (0 : ℝ)..t, ‖A s‖ * ‖(z - w) s‖ := by
    have hInt {f : ℝ → State P.dimension} (hf : IntegrableOn f (Icc 0 T)) :
        IntervalIntegrable f volume 0 t :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1 (by finiteness)).mpr
        (hf.mono_set (Icc_subset_Icc_right ht.2))
    have hdiff : (z - w) t = ∫ s in (0 : ℝ)..t, (generator P (u s)).mulVec ((z - w) s) := by
      simp_rw [Pi.sub_apply, Matrix.mulVec_sub]
      rw [hZ t ht, hW t ht, intervalIntegral.integral_sub
        (hInt (integrableOn_generator_mulVec P hu hz))
        (hInt (integrableOn_generator_mulVec P hu hw))]
      abel
    rw [hdiff, zero_add]
    apply (intervalIntegral.norm_integral_le_integral_norm ht.1).trans
    have hM := (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1 (by finiteness)).mpr
      ((hAnorm.mul_continuousOn (hz.sub hw).norm isCompact_Icc).mono_set
        (Icc_subset_Icc_right ht.2))
    exact intervalIntegral.integral_mono_on ht.1
      (hInt (integrableOn_generator_mulVec P hu (hz.sub hw))).norm hM
      (fun s _ => (A s).le_opNorm ((z - w) s))
  intro t ht
  have h := le_mul_exp_integral_of_le_add_integral hT (hz.sub hw).norm
    hAnorm (fun _ _ => norm_nonneg _) hBound ht
  rw [zero_mul] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

private noncomputable def controlEndomorphism (P : Plant ℝ) :
    (Fin P.controls → ℝ) →L[ℝ] (State P.dimension →L[ℝ] State P.dimension) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => ∑ i, v i • matrixEndomorphism _ (P.control i)
      map_add' := fun v w => by simp [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun c v => by simp [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum] }

private theorem generatorEndomorphism_sub (P : Plant ℝ) (v u : Fin P.controls → ℝ) :
    matrixEndomorphism _ (generator P v) - matrixEndomorphism _ (generator P u) =
      controlEndomorphism P (v - u) := by
  simp only [generator, map_add, map_sum, map_smul, add_sub_add_left_eq_sub]
  change (∑ i, v i • matrixEndomorphism _ (P.control i)) -
      (∑ i, u i • matrixEndomorphism _ (P.control i)) =
    ∑ i, (v i - u i) • matrixEndomorphism _ (P.control i)
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ =>
    (sub_smul (v i) (u i) (matrixEndomorphism _ (P.control i))).symm

private theorem tendsto_generatorEndomorphism_L1 (P : Plant ℝ) {T : ℝ} (hT : 0 ≤ T)
    {u : ℝ → Fin P.controls → ℝ} {v : ℕ → ℝ → Fin P.controls → ℝ}
    (hu : IntegrableOn u (Icc 0 T)) (hv : ∀ j, IntegrableOn (v j) (Icc 0 T))
    (hconv : Tendsto (fun j => ∫ s in (0 : ℝ)..T, ‖v j s - u s‖) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ s in (0 : ℝ)..T,
      ‖matrixEndomorphism _ (generator P (v j s)) -
        matrixEndomorphism _ (generator P (u s))‖) atTop (𝓝 0) := by
  let L := controlEndomorphism P
  have hUpper : Tendsto (fun j => ‖L‖ * ∫ s in (0 : ℝ)..T, ‖v j s - u s‖) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hconv
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper (fun j => ?_)
    (fun j => ?_)
  · exact intervalIntegral.integral_nonneg_of_forall hT (fun _ => norm_nonneg _)
  · rw [← intervalIntegral.integral_const_mul]
    have hM := (integrableOn_generatorEndomorphism P (hv j)).sub
      (integrableOn_generatorEndomorphism P hu)
    have hmI := (intervalIntegrable_iff_integrableOn_Icc_of_le hT (by finiteness)).mpr hM.norm
    have hvI := (intervalIntegrable_iff_integrableOn_Icc_of_le hT (by finiteness)).mpr
      (((hv j).sub hu).norm.const_mul ‖L‖)
    apply intervalIntegral.integral_mono_on hT hmI hvI
    intro t _
    change ‖matrixEndomorphism _ (generator P (v j t)) -
      matrixEndomorphism _ (generator P (u t))‖ ≤ ‖L‖ * ‖v j t - u t‖
    rw [generatorEndomorphism_sub]
    exact L.le_opNorm _

/-- Convergence in L1 of the controls gives convergence of the states with the
same initial value, by uniform convergence of the fundamental solutions. -/
theorem exists_integralSolutions_tendsto_of_control_L1 (P : Plant ℝ) {T : ℝ}
    (hT : 0 ≤ T) {u : ℝ → Fin P.controls → ℝ} {v : ℕ → ℝ → Fin P.controls → ℝ}
    (hu : IntegrableOn u (Icc 0 T)) (hv : ∀ j, IntegrableOn (v j) (Icc 0 T))
    (hconv : Tendsto (fun j => ∫ s in (0 : ℝ)..T, ‖v j s - u s‖) atTop (𝓝 0))
    {x : State P.dimension} {z : ℝ → State P.dimension}
    (hz : ContinuousOn z (Icc 0 T))
    (hEq : ∀ t ∈ Icc 0 T, z t = x + ∫ s in (0 : ℝ)..t, (generator P (u s)).mulVec (z s)) :
    ∃ w : ℕ → ℝ → State P.dimension,
      (∀ j, ContinuousOn (w j) (Icc 0 T)) ∧
      (∀ j t, t ∈ Icc 0 T → w j t =
        x + ∫ s in (0 : ℝ)..t, (generator P (v j s)).mulVec (w j s)) ∧
      ∀ t ∈ Icc 0 T, Tendsto (fun j => w j t) atTop (𝓝 (z t)) := by
  classical
  let E := State P.dimension
  let A (v : ℝ → Fin P.controls → ℝ) (s : ℝ) := matrixEndomorphism P.dimension (generator P (v s))
  have hA (v) (h : IntegrableOn v (Icc 0 T)) : IntegrableOn (A v) (Icc 0 T) :=
    integrableOn_generatorEndomorphism P h
  obtain ⟨Y, hY, hYeq⟩ := exists_continuousOn_of_integrable_linear_equation hT (hA u hu)
    (1 : E →L[ℝ] E)
  choose X hX hXeq using fun j => exists_continuousOn_of_integrable_linear_equation hT
    (hA (v j) (hv j)) (1 : E →L[ℝ] E)
  have hlim := tendstoUniformlyOn_of_integrable_linear_equations hT
    (fun j => hA (v j) (hv j)) (hA u hu) hX hY hXeq hYeq
    (tendsto_generatorEndomorphism_L1 P hT hu hv hconv)
  let L := ContinuousLinearMap.apply ℝ E x
  have hsolution (v) (hv : IntegrableOn v (Icc 0 T)) (B : ℝ → E →L[ℝ] E)
      (hB : ContinuousOn B (Icc 0 T))
      (hBeq : ∀ t ∈ Icc 0 T, B t = 1 + ∫ s in (0 : ℝ)..t, A v s * B s)
      (t) (ht : t ∈ Icc 0 T) :
      L (B t) = x + ∫ s in (0 : ℝ)..t, (generator P (v s)).mulVec (L (B s)) := by
    have hInt : IntervalIntegrable (fun s => A v s * B s) volume 0 t :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1 (by finiteness)).mpr
        (((hA v hv).mul_continuousOn hB isCompact_Icc).mono_set (Icc_subset_Icc_right ht.2))
    have h := congrArg L (hBeq t ht)
    rw [L.map_add, ← L.intervalIntegral_comp_comm hInt] at h
    exact h
  have hYz := eqOn_of_integralSolutions P hT hu
    (L.continuous.comp_continuousOn hY) hz (hsolution u hu Y hY hYeq) hEq
  refine ⟨fun j t => L (X j t), fun j => L.continuous.comp_continuousOn (hX j),
    fun j => hsolution (v j) (hv j) (X j) (hX j) (hXeq j), fun t ht => ?_⟩
  have h := (L.continuous.tendsto (Y t)).comp (hlim.tendsto_at ht)
  rw [show L (Y t) = z t from hYz ht] at h
  exact h

/-- A finite-horizon integrable control has a unique Carathéodory trajectory
on that horizon for each initial state. -/
theorem exists_uniqueOn_caratheodory_trajectory (P : Plant ℝ) {T : ℝ}
    (hT : 0 ≤ T) {u : ℝ → Fin P.controls → ℝ} (hu : IntegrableOn u (Icc 0 T))
    (x : State P.dimension) :
    ∃ z : ℝ → State P.dimension,
      z 0 = x ∧ AbsolutelyContinuousOnInterval z 0 T ∧
      (∀ᵐ t, t ∈ Icc 0 T → HasDerivAt z ((generator P (u t)).mulVec (z t)) t) ∧
      ∀ w : ℝ → State P.dimension, w 0 = x → AbsolutelyContinuousOnInterval w 0 T →
        (∀ᵐ t, t ∈ Icc 0 T → HasDerivAt w ((generator P (u t)).mulVec (w t)) t) →
        EqOn z w (Icc 0 T) := by
  obtain ⟨z, hz, hEq⟩ := exists_integralSolution P hT hu x
  have h0 : z 0 = x := by simpa using hEq 0 ⟨le_rfl, hT⟩
  have hCar (v : ℝ → State P.dimension) :=
    integralEquation_iff_absolutelyContinuous_and_ae_hasDerivAt P hT hu (z := v)
  have hC := (hCar z).mp ⟨hz, by simpa only [h0] using hEq⟩
  refine ⟨z, h0, hC.1, hC.2, fun w hw₀ hw hD => ?_⟩
  obtain ⟨hwc, hW⟩ := (hCar w).mpr ⟨hw, hD⟩
  exact eqOn_of_integralSolutions P hT hu hz hwc hEq (by simpa only [hw₀] using hW)

end ContinuousBilinear
