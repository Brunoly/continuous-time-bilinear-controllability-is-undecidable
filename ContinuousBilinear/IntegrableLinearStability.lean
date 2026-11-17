import ContinuousBilinear.IntegrableGronwall
import ContinuousBilinear.IntegrableLinearExistence
import ContinuousBilinear.Definitions
import Mathlib.Topology.MetricSpace.Pseudo.Basic

namespace ContinuousBilinear

open Set MeasureTheory Filter
open scoped Interval Topology

private theorem intervalIntegrable_of_integrableOn_subinterval
    {E : Type*} [NormedAddCommGroup E] {a b v : ℝ} {g : ℝ → E}
    (hg : IntegrableOn g (Icc a b)) (hv : v ∈ Icc a b) :
    IntervalIntegrable g volume a v :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hv.1 (by finiteness)).2
    (hg.mono_set (Icc_subset_Icc_right hv.2))

section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

private theorem integral_norm_le_of_compact_subinterval {a b : ℝ} {f : ℝ → ℝ}
    (h : IntervalIntegrable f volume a b) (hf : ∀ s, 0 ≤ f s) {t : ℝ}
    (ht : t ∈ Icc a b) :
    (∫ s in a..t, f s) ≤ ∫ s in a..b, f s :=
  intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 (ae_of_all _ hf) h

/-- Growth bound for a solution of a linear integral equation with an
integrable matrix coefficient. -/
theorem norm_le_mul_exp_integral_norm_of_linear_equation
    {a b : ℝ} {M X : ℝ → A} {x₀ : A}
    (hab : a ≤ b) (hM : IntegrableOn M (Icc a b))
    (hX : ContinuousOn X (Icc a b))
    (hEq : ∀ t ∈ Icc a b, X t = x₀ + ∫ s in a..t, M s * X s)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖X t‖ ≤ ‖x₀‖ * Real.exp (∫ s in a..t, ‖M s‖) := by
  have hMnorm : IntegrableOn (fun s => ‖M s‖) (Icc a b) := hM.norm
  apply le_mul_exp_integral_of_le_add_integral hab hX.norm hMnorm
    (fun _ _ => norm_nonneg _) ?_ ht
  intro v hv
  have hMX := intervalIntegrable_of_integrableOn_subinterval
    (hM.mul_continuousOn hX isCompact_Icc) hv
  have hN := intervalIntegrable_of_integrableOn_subinterval
    (hMnorm.mul_continuousOn hX.norm isCompact_Icc) hv
  rw [hEq v hv]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  exact (intervalIntegral.norm_integral_le_integral_norm hv.1).trans
    (intervalIntegral.integral_mono_on hv.1 hMX.norm hN fun _ _ => norm_mul_le _ _)

/-- Stability of linear integral equations on a compact interval under
integrable perturbations of the coefficient, with a common initial condition. -/
theorem norm_sub_le_of_integrable_linear_equations {a b : ℝ}
    {M N X Y : ℝ → A} {x₀ : A} {R : ℝ}
    (hab : a ≤ b) (hM : IntegrableOn M (Icc a b)) (hN : IntegrableOn N (Icc a b))
    (hX : ContinuousOn X (Icc a b)) (hY : ContinuousOn Y (Icc a b))
    (hXeq : ∀ t ∈ Icc a b, X t = x₀ + ∫ s in a..t, M s * X s)
    (hYeq : ∀ t ∈ Icc a b, Y t = x₀ + ∫ s in a..t, N s * Y s)
    (hR : 0 ≤ R) (hYbound : ∀ t ∈ Icc a b, ‖Y t‖ ≤ R)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ‖X t - Y t‖ ≤ (R * (∫ s in a..b, ‖M s - N s‖)) *
      Real.exp (∫ s in a..b, ‖M s‖) := by
  let C := R * (∫ s in a..b, ‖M s - N s‖)
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hMN : IntegrableOn (fun s => ‖M s - N s‖) (Icc a b) := (hM.sub hN).norm
  have hC : 0 ≤ C := mul_nonneg hR
    (intervalIntegral.integral_nonneg_of_forall hab fun _ => norm_nonneg _)
  have hineq (v : ℝ) (hv : v ∈ Icc a b) :
      ‖X v - Y v‖ ≤ C + ∫ s in a..v, ‖M s‖ * ‖X s - Y s‖ := by
    let g (s : ℝ) := M s * X s - N s * Y s
    have hgOn : IntegrableOn g (Icc a b) :=
      (hM.mul_continuousOn hX isCompact_Icc).sub (hN.mul_continuousOn hY isCompact_Icc)
    have hMX := intervalIntegrable_of_integrableOn_subinterval (hM.mul_continuousOn hX isCompact_Icc) hv
    have hNY := intervalIntegrable_of_integrableOn_subinterval (hN.mul_continuousOn hY isCompact_Icc) hv
    have heq : X v - Y v = ∫ s in a..v, g s := by
      rw [hXeq v hv, hYeq v hv, intervalIntegral.integral_sub hMX hNY]
      abel
    have hMnorm : IntegrableOn (fun s => ‖M s‖) (Icc a b) := hM.norm
    have h1 : IntervalIntegrable (fun s => ‖M s‖ * ‖X s - Y s‖) volume a v :=
      intervalIntegrable_of_integrableOn_subinterval
        (hMnorm.mul_continuousOn (hX.sub hY).norm isCompact_Icc) hv
    have h2 : IntervalIntegrable (fun s => R * ‖M s - N s‖) volume a v :=
      intervalIntegrable_of_integrableOn_subinterval (hMN.const_mul R) hv
    have hnorm (s : ℝ) (hs : s ∈ Icc a v) :
        ‖g s‖ ≤ ‖M s‖ * ‖X s - Y s‖ + R * ‖M s - N s‖ := by
      have he : g s = M s * (X s - Y s) + (M s - N s) * Y s := by
        simp only [g, mul_sub, sub_mul]
        abel
      rw [he]
      calc
        _ ≤ ‖M s * (X s - Y s)‖ + ‖(M s - N s) * Y s‖ := norm_add_le _ _
        _ ≤ ‖M s‖ * ‖X s - Y s‖ + ‖M s - N s‖ * ‖Y s‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ _ := by
          rw [mul_comm R]
          exact add_le_add le_rfl
            (mul_le_mul_of_nonneg_left (hYbound s (Icc_subset_Icc_right hv.2 hs))
              (norm_nonneg (M s - N s)))
    have hperturb : R * (∫ s in a..v, ‖M s - N s‖) ≤ C :=
      mul_le_mul_of_nonneg_left
        (integral_norm_le_of_compact_subinterval (intervalIntegrable_of_integrableOn_subinterval hMN hb) (fun _ => norm_nonneg _) hv) hR
    calc
      _ = ‖∫ s in a..v, g s‖ := by rw [heq]
      _ ≤ ∫ s in a..v, ‖g s‖ := intervalIntegral.norm_integral_le_integral_norm hv.1
      _ ≤ ∫ s in a..v, ‖M s‖ * ‖X s - Y s‖ + R * ‖M s - N s‖ :=
        intervalIntegral.integral_mono_on hv.1 (intervalIntegrable_of_integrableOn_subinterval hgOn hv).norm (h1.add h2) hnorm
      _ ≤ _ := by
        rw [intervalIntegral.integral_add h1 h2, intervalIntegral.integral_const_mul]
        linarith
  have hg := le_mul_exp_integral_of_le_add_integral hab (hX.sub hY).norm
    hM.norm (fun _ _ => norm_nonneg _) hineq ht
  exact hg.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
    (integral_norm_le_of_compact_subinterval (intervalIntegrable_of_integrableOn_subinterval hM.norm hb) (fun _ => norm_nonneg _) ht)) hC)

/-- Two continuous solutions of the same linear integral equation with the
same initial condition agree on the interval. -/
theorem eqOn_of_integrable_linear_equations {a b : ℝ} {M X Y : ℝ → A} {x₀ : A}
    (hab : a ≤ b) (hM : IntegrableOn M (Icc a b))
    (hX : ContinuousOn X (Icc a b)) (hY : ContinuousOn Y (Icc a b))
    (hXeq : ∀ t ∈ Icc a b, X t = x₀ + ∫ s in a..t, M s * X s)
    (hYeq : ∀ t ∈ Icc a b, Y t = x₀ + ∫ s in a..t, M s * Y s) :
    EqOn X Y (Icc a b) := by
  obtain ⟨r, _, hmax⟩ := isCompact_Icc.exists_isMaxOn
    ⟨a, left_mem_Icc.mpr hab⟩ hY.norm
  intro t ht
  have h := norm_sub_le_of_integrable_linear_equations hab hM hM hX hY hXeq hYeq
    (norm_nonneg (Y r)) (fun s hs => hmax hs) ht
  simp only [sub_self, norm_zero, intervalIntegral.integral_zero, mul_zero, zero_mul] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

/-- A linear equation with an integrable coefficient and a prescribed initial
value has a continuous solution, unique on its time interval. -/
theorem exists_uniqueOn_of_integrable_linear_equation [CompleteSpace A]
    {a b : ℝ} (hab : a ≤ b) {M : ℝ → A} (hM : IntegrableOn M (Icc a b)) (x₀ : A) :
    ∃ X : ℝ → A, ContinuousOn X (Icc a b) ∧
      (∀ t ∈ Icc a b, X t = x₀ + ∫ s in a..t, M s * X s) ∧
      ∀ Y : ℝ → A, ContinuousOn Y (Icc a b) →
        (∀ t ∈ Icc a b, Y t = x₀ + ∫ s in a..t, M s * Y s) →
        EqOn X Y (Icc a b) := by
  obtain ⟨X, hX, hEq⟩ := exists_continuousOn_of_integrable_linear_equation hab hM x₀
  exact ⟨X, hX, hEq, fun _ hY hYeq => eqOn_of_integrable_linear_equations hab hM hX hY hEq hYeq⟩

/-- Continuous dependence of the fundamental solution on the coefficient in
the L1 norm. The initial matrix can be chosen to be the identity. -/
theorem tendstoUniformlyOn_of_integrable_linear_equations {a b : ℝ}
    {M : ℕ → ℝ → A} {N Y : ℝ → A} {X : ℕ → ℝ → A} {x₀ : A}
    (hab : a ≤ b) (hM : ∀ j, IntegrableOn (M j) (Icc a b))
    (hN : IntegrableOn N (Icc a b)) (hX : ∀ j, ContinuousOn (X j) (Icc a b))
    (hY : ContinuousOn Y (Icc a b))
    (hXeq : ∀ j t, t ∈ Icc a b → X j t = x₀ + ∫ s in a..t, M j s * X j s)
    (hYeq : ∀ t ∈ Icc a b, Y t = x₀ + ∫ s in a..t, N s * Y s)
    (hconv : Tendsto (fun j => ∫ s in a..b, ‖M j s - N s‖) atTop (𝓝 0)) :
    TendstoUniformlyOn X Y atTop (Icc a b) := by
  obtain ⟨r, hr, hmax⟩ := isCompact_Icc.exists_isMaxOn
    ⟨a, left_mem_Icc.mpr hab⟩ hY.norm
  let R := ‖Y r‖
  have hR : 0 ≤ R := norm_nonneg _
  let B := ∫ s in a..b, ‖N s‖
  let δ (j : ℕ) := ∫ s in a..b, ‖M j s - N s‖
  have hδ (j : ℕ) : 0 ≤ δ j := intervalIntegral.integral_nonneg_of_forall hab
    (fun _ => norm_nonneg _)
  have hBound (j : ℕ) : (∫ s in a..b, ‖M j s‖) ≤ B + δ j := by
    have hNI := (intervalIntegrable_iff_integrableOn_Icc_of_le hab (by finiteness)).2 hN.norm
    have hMI := (intervalIntegrable_iff_integrableOn_Icc_of_le hab (by finiteness)).2
      (hM j).norm
    have hDI := (intervalIntegrable_iff_integrableOn_Icc_of_le hab (by finiteness)).2
      ((hM j).sub hN).norm
    rw [show B + δ j = ∫ s in a..b, ‖N s‖ + ‖M j s - N s‖ from
      (intervalIntegral.integral_add hNI hDI).symm]
    exact intervalIntegral.integral_mono_on hab hMI (hNI.add hDI) (fun s _ => by
      simpa only [sub_add_cancel] using (norm_add_le (M j s - N s) (N s)).trans_eq (add_comm _ _))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hsmall : ∀ᶠ j in atTop, δ j < 1 := hconv.eventually (gt_mem_nhds zero_lt_one)
  have hscaled : Tendsto (fun j => (R * δ j) * Real.exp (B + 1)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      (tendsto_const_nhds.mul hconv).mul
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => Real.exp (B + 1)) atTop _)
  filter_upwards [hsmall, hscaled.eventually (gt_mem_nhds hε)] with j hj hjε t ht
  rw [dist_comm, dist_eq_norm]
  apply lt_of_le_of_lt (norm_sub_le_of_integrable_linear_equations hab (hM j) hN
    (hX j) hY (hXeq j) hYeq hR (fun s hs => hmax hs) ht)
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr ((hBound j).trans (add_le_add_right hj.le B)))
    (mul_nonneg hR (hδ j))) hjε

end

noncomputable section

open scoped Matrix.Norms.Operator

local instance (n : ℕ) : ContinuousENorm (RealMatrix n) :=
  (@SeminormedAddGroup.toESeminormedAddMonoid (RealMatrix n)
    Matrix.linftyOpSeminormedAddCommGroup.toSeminormedAddGroup).toContinuousENorm

/-- Continuous dependence of fundamental matrices under L1 convergence of
matrix coefficients. -/
theorem tendstoUniformlyOn_fundamentalMatrix_of_integrable {n : ℕ} {T : ℝ}
    {M : ℕ → ℝ → RealMatrix n} {N Y : ℝ → RealMatrix n} {X : ℕ → ℝ → RealMatrix n}
    (hT : 0 ≤ T) (hM : ∀ j, IntegrableOn (M j) (Icc 0 T))
    (hN : IntegrableOn N (Icc 0 T)) (hX : ∀ j, ContinuousOn (X j) (Icc 0 T))
    (hY : ContinuousOn Y (Icc 0 T))
    (hXeq : ∀ j t, t ∈ Icc 0 T → X j t = 1 + ∫ s in (0 : ℝ)..t, M j s * X j s)
    (hYeq : ∀ t ∈ Icc 0 T, Y t = 1 + ∫ s in (0 : ℝ)..t, N s * Y s)
    (hconv : Tendsto (fun j => ∫ s in (0 : ℝ)..T, ‖M j s - N s‖) atTop (𝓝 0)) :
    TendstoUniformlyOn X Y atTop (Icc 0 T) :=
  tendstoUniformlyOn_of_integrable_linear_equations hT hM hN hX hY hXeq hYeq hconv

end

end ContinuousBilinear
