import ContinuousBilinear.SignEncodingGradient
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Order.Round

namespace ContinuousBilinear
namespace IntegerPolynomialCode

open scoped Real
open MvPolynomial

private theorem degree_le (p : IntegerPolynomialCode) {a : Fin p.arity →₀ ℕ}
    (ha : a ∈ p.denote.support) :
    (∑ i, a i) ≤ p.homogenizingDegree := by
  rw [← Finsupp.sum_fintype a (fun _ e => e) (fun _ => rfl)]
  exact (MvPolynomial.le_totalDegree ha).trans (le_max_right _ _)

/-- Evaluating the homogenization on an integer ray recovers the original polynomial. -/
theorem homogenizedValue_integerRay (p : IntegerPolynomialCode) (t : ℝ)
    (x : Fin p.arity → ℤ) :
    p.homogenizedValue (Fin.cases t (fun i => t * (x i : ℝ))) =
      t ^ p.homogenizingDegree * (MvPolynomial.eval x p.denote : ℝ) := by
  classical
  rw [homogenizedValue]
  change _ = _ * (Int.castRingHom ℝ) (MvPolynomial.eval x p.denote)
  rw [show MvPolynomial.eval x p.denote = p.denote.eval₂ (RingHom.id ℤ) x from rfl,
      MvPolynomial.eval₂_eq']
  simp only [map_sum, map_mul, map_prod, map_pow, RingHom.id_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [Fin.cases_zero, Fin.cases_succ, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finsupp.sum_fintype a (fun _ e => e) (fun _ => rfl)]
  rw [mul_assoc, ← mul_assoc (t ^ _) (t ^ _), ← pow_add, Nat.sub_add_cancel (degree_le p ha)]
  change (p.denote.coeff a : ℝ) * (t ^ p.homogenizingDegree *
      ∏ i, (x i : ℝ) ^ a i) = t ^ p.homogenizingDegree *
      ((p.denote.coeff a : ℝ) * ∏ i, (x i : ℝ) ^ a i)
  ring

/-- An integer zero yields a strictly negative value on the oscillator graph. -/
theorem exists_negative_of_hasIntegerRoot (p : IntegerPolynomialCode)
    (h : p.HasIntegerRoot) :
    ∃ (q : Fin (p.arity + 1) → ℝ) (a : ℝ),
      p.signPolynomialValue q (fun i => Real.sin (q i)) a < 0 := by
  obtain ⟨x, hx⟩ := h
  let q : Fin (p.arity + 1) → ℝ := Fin.cases π (fun i => π * (x i : ℝ))
  let a := Real.sqrt ((π - 3) * (4 - π))
  have hnonneg : 0 ≤ (π - 3) * (4 - π) :=
    mul_nonneg (sub_nonneg.mpr Real.pi_gt_three.le) (sub_nonneg.mpr Real.pi_lt_four.le)
  have hQ : p.homogenizedValue q = 0 := by
    dsimp only [q]
    rw [homogenizedValue_integerRay, hx, Int.cast_zero, mul_zero]
  have hs : ∀ i, Real.sin (q i) = 0 := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [q]
    · dsimp only [q]
      rw [Fin.cases_succ, mul_comm]
      exact Real.sin_int_mul_pi _
  refine ⟨q, a, ?_⟩
  simp [signPolynomialValue, hQ, hs, q, a, Real.sq_sqrt hnonneg]

/-- The nearest integer multiple of pi obeys a quantitative bound from Jordan's inequality. -/
theorem abs_sub_round_pi_mul_le (x : ℝ) :
    |x - (round (x / π) : ℝ) * π| ≤ π / 2 * |Real.sin x| := by
  let k := round (x / π)
  have hp : 0 < π := Real.pi_pos
  have he : x - (k : ℝ) * π = (x / π - (k : ℝ)) * π := by
    field_simp
  have hb : |x - (k : ℝ) * π| ≤ π / 2 := by
    rw [he, abs_mul, abs_of_pos hp]
    have hm := mul_le_mul_of_nonneg_right (abs_sub_round (x / π)) hp.le
    change |x / π - (k : ℝ)| * π ≤ (1 / 2) * π at hm
    linarith
  have hj := Real.mul_abs_le_abs_sin hb
  rw [Real.sin_sub_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul] at hj
  change |x - (k : ℝ) * π| ≤ _
  have hj' : 2 * |x - (k : ℝ) * π| ≤ |Real.sin x| * π :=
    (div_le_iff₀ hp).mp (by simpa only [div_mul_eq_mul_div] using hj)
  linarith

theorem hasIntegerRoot_of_negative (p : IntegerPolynomialCode)
    (q : Fin (p.arity + 1) → ℝ) (a : ℝ)
    (h : p.signPolynomialValue q (fun i => Real.sin (q i)) a < 0) :
    p.HasIntegerRoot := by
  let d := p.homogenizingDegree
  let H : ℝ := p.coefficientHeight
  let κ : ℝ := p.signScale
  let R : ℝ := 1 + ∑ i, q i ^ 2
  let g := (q 0 - 3) * (4 - q 0) - a ^ 2
  let S : ℝ := Real.sqrt R
  let k : Fin (p.arity + 1) → ℤ := fun i => round (q i / π)
  let q' : Fin (p.arity + 1) → ℝ := fun i => (k i : ℝ) * π
  have hd : 1 ≤ d := le_max_left _ _
  have hH : 0 ≤ H := by
    dsimp only [H, coefficientHeight]
    positivity
  have hκ : κ = 2 ^ (d + 1) * (d : ℝ) * (H + 1) := by
    dsimp only [κ, signScale, d, H]
    push_cast
    rfl
  have hκ4 : 4 ≤ κ := by
    rw [hκ]
    have hpow : (4 : ℝ) ≤ 2 ^ (d + 1) := by
      calc
        4 = (2 : ℝ)^2 := by norm_num
        _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
    calc
      4 = (4 : ℝ) * 1 * 1 := by norm_num
      _ ≤ _ := by
        gcongr
        linarith
  have hκpos : 0 < κ := by linarith
  have hR : 1 ≤ R := le_add_of_nonneg_right (by positivity)
  have hRpos : 0 < R := by linarith
  have hSsq : S ^ 2 = R := Real.sq_sqrt hRpos.le
  have hS : 1 ≤ S := by
    have hs : 0 ≤ S := Real.sqrt_nonneg _
    nlinarith
  have hSpos : 0 < S := by linarith
  let W := κ * S ^ (d - 1)
  have hW : κ ≤ W := by
    calc
      κ = κ * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (one_le_pow₀ hS) hκpos.le
  have hWpos : 0 < W := hκpos.trans_le hW
  have hWs : W ^ 2 = κ ^ 2 * R ^ (d - 1) := by
    rw [mul_pow, ← pow_mul, mul_comm (d - 1) 2, pow_mul, hSsq]
  change p.homogenizedValue q ^ 2 + κ ^ 2 * R ^ (d - 1) *
    ((∑ i, Real.sin (q i) ^ 2) + g ^ 2) - 1 < 0 at h
  rw [← hWs] at h
  have hsum : 0 ≤ ∑ i, Real.sin (q i) ^ 2 := by positivity
  have hQ : |p.homogenizedValue q| < 1 := by
    have hh : p.homogenizedValue q ^ 2 < (1 : ℝ)^2 := by
      have : 0 ≤ W ^ 2 * ((∑ i, Real.sin (q i) ^ 2) + g ^ 2) := by positivity
      linarith
    simpa only [abs_one] using sq_lt_sq.mp hh
  have hsmall {u : ℝ} (hu : u ^ 2 ≤ (∑ i, Real.sin (q i) ^ 2) + g ^ 2) :
      |u| < 1 / W := by
    have hh := mul_le_mul_of_nonneg_left hu (sq_nonneg W)
    have hw : W ^ 2 * u ^ 2 < 1 := by nlinarith [sq_nonneg (p.homogenizedValue q)]
    have hm : |W * u| < |(1 : ℝ)| := sq_lt_sq.mp (by rw [mul_pow, one_pow]; exact hw)
    rw [abs_mul, abs_of_pos hWpos, abs_one, mul_comm] at hm
    exact (lt_div_iff₀ hWpos).2 hm
  have hg : |g| < 1 / 4 := (hsmall (by linarith : g ^ 2 ≤ _)).trans_le
    (one_div_le_one_div_of_le (by norm_num) (hκ4.trans hW))
  have hg' := (abs_lt.mp hg).1
  have hq0lo : 2 < q 0 := by
    by_contra! hlo
    have hn := mul_nonneg (show 0 ≤ 2 - q 0 by linarith) (show 0 ≤ 5 - q 0 by linarith)
    dsimp only [g] at hg'
    nlinarith [sq_nonneg a]
  have hq0hi : q 0 < 5 := by
    by_contra! hhi
    have hn := mul_nonneg (show 0 ≤ q 0 - 5 by linarith) (show 0 ≤ q 0 - 2 by linarith)
    dsimp only [g] at hg'
    nlinarith [sq_nonneg a]
  have herr (i) : |q i - q' i| ≤ 2 / W := by
    have hi : Real.sin (q i) ^ 2 ≤ ∑ j, Real.sin (q j) ^ 2 :=
      Finset.single_le_sum (f := fun j => Real.sin (q j) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have hs : |Real.sin (q i)| < 1 / W := hsmall (hi.trans (le_add_of_nonneg_right (sq_nonneg g)))
    calc
      _ ≤ π / 2 * |Real.sin (q i)| := abs_sub_round_pi_mul_le _
      _ ≤ 2 / W := by
        rw [div_eq_mul_inv 2]
        have hpi : π / 2 ≤ 2 := by linarith [Real.pi_lt_four]
        exact mul_le_mul hpi (by simpa only [one_div] using hs.le) (abs_nonneg _) (by norm_num)
  have hhalf (i) : |q i - q' i| ≤ 1 / 2 := (herr i).trans
    ((div_le_iff₀ hWpos).2 (by linarith [hκ4.trans hW]))
  have hk0 : k 0 = 1 := by
    have hval := abs_le.mp (hhalf 0)
    change -(1 / 2 : ℝ) ≤ q 0 - (k 0 : ℝ) * π ∧
      q 0 - (k 0 : ℝ) * π ≤ 1 / 2 at hval
    by_contra hn
    have hc : k 0 ≤ 0 ∨ 2 ≤ k 0 := by omega
    rcases hc with hc | hc
    · have hc' : (k 0 : ℝ) ≤ 0 := by exact_mod_cast hc
      nlinarith [mul_nonpos_of_nonpos_of_nonneg hc' Real.pi_pos.le, hval.2]
    · have hc' : (2 : ℝ) ≤ k 0 := by exact_mod_cast hc
      nlinarith [mul_le_mul_of_nonneg_right hc' Real.pi_pos.le, Real.pi_gt_three, hval.1]
  have hx (i) : |q i| ≤ S := by
    have hi : q i ^ 2 ≤ ∑ j, q j ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have hs : q i ^ 2 ≤ S ^ 2 := by rw [hSsq]; dsimp only [R]; linarith
    exact (sq_le_sq.mp hs).trans_eq (abs_of_pos hSpos)
  have hy (i) : |q' i| ≤ 2 * S := by
    have hdist : |q' i - q i| ≤ 1 / 2 := by simpa only [abs_sub_comm] using hhalf i
    have ht := (abs_sub_abs_le_abs_sub (q' i) (q i)).trans hdist
    linarith [hx i]
  have hlip := p.homogenizedValue_sub_le_meanValue q q' (show 0 ≤ 2 * S by positivity)
    (show 0 ≤ 2 / W by positivity) (fun i => by linarith [hx i]) hy
    (fun i => by simpa only [abs_sub_comm] using herr i)
  change |p.homogenizedValue q' - p.homogenizedValue q| ≤
    (d : ℝ) * H * (2 * S) ^ (d - 1) * (2 / W) at hlip
  have hcalc : (d : ℝ) * H * (2 * S) ^ (d - 1) * (2 / W) =
      H / (2 * (H + 1)) := by
    rw [mul_pow]
    have hHp : H + 1 ≠ 0 := by linarith
    have hdpos : (d : ℝ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
    have hpow : (2 : ℝ) ^ (d + 1) = 2 ^ (d - 1) * 2 * 2 := by
      rw [show d + 1 = (d - 1) + 1 + 1 by omega, pow_succ, pow_succ]
    dsimp only [W]
    rw [hκ, hpow]
    field_simp [hHp, hdpos, hSpos.ne', pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0)] <;> ring
  rw [hcalc] at hlip
  have hlt : H / (2 * (H + 1)) < 1 / 2 :=
    (div_lt_iff₀ (by linarith)).2 (by linarith)
  have hdiff := hlip.trans_lt hlt
  have hQ' : |p.homogenizedValue q'| < 3 / 2 := by
    have hh := abs_sub_abs_le_abs_sub (p.homogenizedValue q') (p.homogenizedValue q)
    linarith
  let x : Fin p.arity → ℤ := fun i => k i.succ
  have hq' : q' = Fin.cases π (fun i => π * (x i : ℝ)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [q', hk0]
    · simp [q', x, mul_comm]
  rw [hq', homogenizedValue_integerRay, abs_mul,
    abs_of_pos (pow_pos Real.pi_pos _)] at hQ'
  refine ⟨x, ?_⟩
  by_contra hne
  have hi : (1 : ℤ) ≤ |MvPolynomial.eval x p.denote| :=
    Int.add_one_le_iff.mpr (abs_pos.mpr hne)
  have hi' : (1 : ℝ) ≤ |(MvPolynomial.eval x p.denote : ℝ)| := by exact_mod_cast hi
  have hpow : π ≤ π ^ p.homogenizingDegree := by
    rw [← pow_one π]
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith [Real.pi_gt_three] : 1 ≤ π) hd
  have := mul_le_mul hpow hi' zero_le_one (pow_nonneg Real.pi_pos.le _)
  linarith [Real.pi_gt_three]

end IntegerPolynomialCode

namespace Targets

theorem signEncoding : SignEncoding := by
  intro p
  exact ⟨fun ⟨q, a, h⟩ => p.hasIntegerRoot_of_negative q a h,
    p.exists_negative_of_hasIntegerRoot⟩

end Targets
end ContinuousBilinear
