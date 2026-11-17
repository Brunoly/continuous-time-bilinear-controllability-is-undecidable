import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul

open Filter Asymptotics
open scoped Topology

namespace ContinuousBilinear

private theorem norm_pow_sub_pow_le {A : Type*} [NormedRing A] [NormOneClass A]
    {x y : A} {r : ℝ} (hr : 1 ≤ r) (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) (n : ℕ) :
    ‖x ^ n - y ^ n‖ ≤ n * r ^ n * ‖x - y‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hr0 : 0 ≤ r := zero_le_one.trans hr
    have hxn : ‖x ^ n‖ ≤ r ^ n :=
      (norm_pow_le _ _).trans (pow_le_pow_left₀ (norm_nonneg _) hx _)
    have hp : r ^ n ≤ r ^ (n + 1) := by
      rw [pow_succ]
      exact le_mul_of_one_le_right (pow_nonneg hr0 _) hr
    rw [pow_succ x, pow_succ y,
      show x ^ n * x - y ^ n * y = x ^ n * (x - y) + (x ^ n - y ^ n) * y by
        simp only [mul_sub, sub_mul]; abel]
    calc
      _ ≤ ‖x ^ n * (x - y)‖ + ‖(x ^ n - y ^ n) * y‖ := norm_add_le _ _
      _ ≤ r ^ n * ‖x - y‖ + (n * r ^ n * ‖x - y‖) * r := by
        exact add_le_add ((norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hxn (norm_nonneg _)))
          ((norm_mul_le _ _).trans (mul_le_mul ih hy (norm_nonneg _) (by positivity)))
      _ ≤ r ^ (n + 1) * ‖x - y‖ + (n * r ^ n * ‖x - y‖) * r :=
        add_le_add_left (mul_le_mul_of_nonneg_right hp (norm_nonneg _)) _
      _ = (↑(n + 1) : ℝ) * r ^ (n + 1) * ‖x - y‖ := by push_cast; rw [pow_succ]; ring

private theorem norm_le_one_add_of_hasDerivAt {A : Type*}
    [NormedRing A] [NormOneClass A] [NormedAlgebra ℝ A]
    {f : ℝ → A} {a : A} (hf : HasDerivAt f a 0) (h0 : f 0 = 1) :
    ∀ᶠ h in 𝓝 0, ‖f h‖ ≤ 1 + (‖a‖ + 1) * ‖h‖ := by
  have hb := hf.isLittleO.bound (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hb] with h hSmall
  have heq : f h = (f h - f 0 - (h - 0) • a) + f 0 + (h - 0) • a := by abel
  calc
    ‖f h‖ ≤ ‖f h - f 0 - (h - 0) • a‖ + ‖f 0‖ + ‖(h - 0) • a‖ := by
      conv_lhs => rw [heq]
      exact (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
    _ ≤ 1 + (‖a‖ + 1) * ‖h‖ := by
      rw [h0, norm_one, sub_zero, norm_smul]
      simp only [sub_zero, one_mul, h0] at hSmall
      nlinarith [hSmall]

/-- Powers of a differentiable path through the identity converge to the exponential
of its derivative when the time step is the reciprocal of the number of factors. -/
theorem tendsto_pow_inv_nat_of_hasDerivAt {A : Type*} [NormedRing A] [NormOneClass A]
    [NormedAlgebra ℝ A] [CompleteSpace A] {f : ℝ → A} {a : A}
    (hf : HasDerivAt f a 0) (h0 : f 0 = 1) :
    Tendsto (fun n : ℕ => f ((n + 1 : ℝ)⁻¹) ^ (n + 1)) atTop
      (𝓝 (NormedSpace.exp a)) := by
  let g : ℝ → A := fun t => NormedSpace.exp (t • a)
  have hg0 : g 0 = 1 := by simp [g]
  have hg : HasDerivAt g a 0 := by
    simpa [g] using hasDerivAt_exp_smul_const a (0 : ℝ)
  have hd := (hf.sub hg).isLittleO
  have hdiff : (fun h : ℝ => f h - g h) =o[𝓝 0] (fun h : ℝ => h) := by
    simpa [h0, hg0] using hd
  let C := ‖a‖ + 1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let t : ℕ → ℝ := fun n => (n + 1 : ℝ)⁻¹
  have ht : Tendsto t atTop (𝓝 0) :=
    by simpa [t, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have htp (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  have htc (n : ℕ) : (↑(n + 1) : ℝ) * t n = 1 := by
    dsimp [t]
    push_cast
    exact mul_inv_cancel₀ (by positivity)
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hgpow (n : ℕ) : g (t n) ^ (n + 1) = NormedSpace.exp a := by
    rw [show g (t n) = NormedSpace.exp (t n • a) from rfl, ← NormedSpace.exp_nsmul,
      ← Nat.cast_smul_eq_nsmul ℝ (n + 1), smul_smul, htc, one_smul]
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hε' : 0 < ε / (2 * Real.exp C) := by positivity
  have hb := ht.eventually (hdiff.bound hε')
  have hF := ht.eventually (norm_le_one_add_of_hasDerivAt hf h0)
  have hG := ht.eventually (norm_le_one_add_of_hasDerivAt hg hg0)
  apply eventually_atTop.mp
  filter_upwards [hb, hF, hG] with n hn hfn hgn
  have hCh : 0 ≤ C * t n := mul_nonneg hC (htp n).le
  have hstep : 1 + C * ‖t n‖ ≤ Real.exp (C * t n) := by
    rw [Real.norm_eq_abs, abs_of_pos (htp n)]
    simpa [add_comm] using Real.add_one_le_exp (C * t n)
  have hr : 1 ≤ Real.exp (C * t n) := Real.one_le_exp hCh
  have hpow : Real.exp (C * t n) ^ (n + 1) = Real.exp C := by
    rw [← Real.exp_nat_mul, mul_comm C, ← mul_assoc, htc, one_mul]
  have hEstimate := norm_pow_sub_pow_le hr (hfn.trans hstep) (hgn.trans hstep) (n + 1)
  rw [hgpow, hpow] at hEstimate
  rw [dist_eq_norm]
  refine hEstimate.trans_lt ?_
  rw [Real.norm_eq_abs, abs_of_pos (htp n)] at hn
  calc
    (↑(n + 1) : ℝ) * Real.exp C * ‖f (t n) - g (t n)‖ ≤
        (↑(n + 1) : ℝ) * Real.exp C * (ε / (2 * Real.exp C) * t n) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    _ = ε / 2 := by
      calc
        _ = ((↑(n + 1) : ℝ) * t n) * (ε / 2) := by
          field_simp [Real.exp_ne_zero]
        _ = _ := by rw [htc, one_mul]
    _ < ε := by linarith

/-- The Lie–Trotter product formula for real Banach algebras. -/
theorem tendsto_lie_trotter {A : Type*} [NormedRing A] [NormOneClass A]
    [NormedAlgebra ℝ A] [CompleteSpace A] (a b : A) :
    Tendsto (fun n : ℕ =>
      (NormedSpace.exp ((n + 1 : ℝ)⁻¹ • a) *
        NormedSpace.exp ((n + 1 : ℝ)⁻¹ • b)) ^ (n + 1))
      atTop (𝓝 (NormedSpace.exp (a + b))) := by
  apply tendsto_pow_inv_nat_of_hasDerivAt (f := fun t : ℝ =>
    NormedSpace.exp (t • a) * NormedSpace.exp (t • b))
  · change HasDerivAt ((fun t : ℝ => NormedSpace.exp (t • a)) *
      (fun t : ℝ => NormedSpace.exp (t • b))) (a + b) 0
    simpa [add_comm] using
      (hasDerivAt_exp_smul_const a (0 : ℝ)).mul
        (hasDerivAt_exp_smul_const b (0 : ℝ))
  · simp

/-- The split Euler step with one affine factor and one exact exponential factor. -/
theorem tendsto_split_euler {A : Type*} [NormedRing A] [NormOneClass A]
    [NormedAlgebra ℝ A] [CompleteSpace A] (a b : A) :
    Tendsto (fun n : ℕ =>
      ((1 + (n + 1 : ℝ)⁻¹ • a) *
        NormedSpace.exp ((n + 1 : ℝ)⁻¹ • b)) ^ (n + 1))
      atTop (𝓝 (NormedSpace.exp (a + b))) := by
  apply tendsto_pow_inv_nat_of_hasDerivAt (f := fun t : ℝ =>
    (1 + t • a) * NormedSpace.exp (t • b))
  · have hAffine : HasDerivAt (fun r : ℝ => 1 + r • a) a 0 := by
      simpa only [id, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add 1
    change HasDerivAt ((fun r : ℝ => 1 + r • a) *
      (fun r : ℝ => NormedSpace.exp (r • b))) (a + b) 0
    simpa [add_comm] using hAffine.mul (hasDerivAt_exp_smul_const b (0 : ℝ))
  · simp

end ContinuousBilinear
