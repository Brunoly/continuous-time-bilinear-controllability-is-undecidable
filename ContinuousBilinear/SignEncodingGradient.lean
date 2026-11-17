import ContinuousBilinear.SignEncoding
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace ContinuousBilinear.IntegerPolynomialCode

open MvPolynomial
open scoped BigOperators

private noncomputable def homogeneousExponents (p : IntegerPolynomialCode) (a : Fin p.arity →₀ ℕ) :
    Fin (p.arity + 1) → ℕ :=
  Fin.cases (p.homogenizingDegree - ∑ i, a i) a

private theorem sum_homogeneousExponents (p : IntegerPolynomialCode)
    {a : Fin p.arity →₀ ℕ} (ha : a ∈ p.denote.support) :
    ∑ i, homogeneousExponents p a i = p.homogenizingDegree := by
  have hdegree : (∑ i, a i) ≤ p.homogenizingDegree := by
    rw [← Finsupp.sum_fintype a (fun _ e => e) (fun _ => rfl)]
    exact (MvPolynomial.le_totalDegree ha).trans (le_max_right _ _)
  rw [Fin.sum_univ_succ]
  simpa [homogeneousExponents] using Nat.sub_add_cancel hdegree

private theorem homogenizedValue_eq_sum (p : IntegerPolynomialCode)
    (q : Fin (p.arity + 1) → ℝ) :
    p.homogenizedValue q =
      ∑ a ∈ p.denote.support, (p.denote.coeff a : ℝ) * ∏ i, q i ^ homogeneousExponents p a i := by
  unfold homogenizedValue
  apply Finset.sum_congr rfl
  intro a _
  rw [Fin.prod_univ_succ, Finsupp.sum_fintype a (fun _ e => e) (fun _ => rfl)]
  simp only [homogeneousExponents, Fin.cases_zero, Fin.cases_succ, mul_assoc]

private noncomputable def monomialPartial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (e : ι → ℕ) (i : ι) : ℝ :=
  (∏ j ∈ Finset.univ.erase i, q j ^ e j) * ((e i : ℝ) * q i ^ (e i - 1))

/-- The coordinate partial derivative of the homogeneous evaluation polynomial. -/
noncomputable def homogenizedPartial (p : IntegerPolynomialCode) (q : Fin (p.arity + 1) → ℝ)
    (i : Fin (p.arity + 1)) : ℝ :=
  ∑ a ∈ p.denote.support, (p.denote.coeff a : ℝ) * monomialPartial q (homogeneousExponents p a) i

private theorem abs_monomialPartial_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℝ) (e : ι → ℕ) (i : ι) {B : ℝ} (hB : 0 ≤ B) (hq : ∀ j, |q j| ≤ B) :
    |monomialPartial q e i| ≤ (e i : ℝ) * B ^ ((∑ j, e j) - 1) := by
  by_cases hzero : e i = 0
  · simp [monomialPartial, hzero]
  have hpow (j : ι) (n : ℕ) : |q j ^ n| ≤ B ^ n := by
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hq j) n
  have hprod : |∏ j ∈ Finset.univ.erase i, q j ^ e j| ≤
      B ^ (∑ j ∈ Finset.univ.erase i, e j) := by
    rw [Finset.abs_prod, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun j _ => hpow j _)
  have hsum : (∑ j ∈ Finset.univ.erase i, e j) + e i = ∑ j, e j :=
    Finset.sum_erase_add _ _ (Finset.mem_univ i)
  have hexp : (∑ j ∈ Finset.univ.erase i, e j) + (e i - 1) = (∑ j, e j) - 1 := by omega
  unfold monomialPartial
  rw [abs_mul, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (e i : ℝ) from Nat.cast_nonneg _)]
  calc
    _ ≤ B ^ (∑ j ∈ Finset.univ.erase i, e j) * ((e i : ℝ) * B ^ (e i - 1)) := by
      exact mul_le_mul hprod (mul_le_mul_of_nonneg_left (hpow i _) (Nat.cast_nonneg _))
        (by positivity) (pow_nonneg hB _)
    _ = (e i : ℝ) * (B ^ (∑ j ∈ Finset.univ.erase i, e j) * B ^ (e i - 1)) := by ring
    _ = _ := by rw [← pow_add, hexp]

/-- On the coordinate box, the sum of absolute coordinate partial derivatives is bounded by
the degree times the coefficient height times the radius to the degree minus one. -/
theorem sum_abs_homogenizedPartial_le (p : IntegerPolynomialCode) (q : Fin (p.arity + 1) → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hq : ∀ i, |q i| ≤ B) :
    ∑ i, |p.homogenizedPartial q i| ≤
      (p.homogenizingDegree : ℝ) * (p.coefficientHeight : ℝ) * B ^ (p.homogenizingDegree - 1) := by
  classical
  unfold homogenizedPartial
  calc
    _ ≤ ∑ i, ∑ a ∈ p.denote.support,
        |(p.denote.coeff a : ℝ)| * ((homogeneousExponents p a i : ℝ) *
          B ^ (p.homogenizingDegree - 1)) := by
      apply Finset.sum_le_sum
      intro i _
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun a ha => ?_))
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [sum_homogeneousExponents p ha] using
        abs_monomialPartial_le q (homogeneousExponents p a) i hB hq
    _ = _ := by
      rw [Finset.sum_comm]
      calc
        _ = ∑ a ∈ p.denote.support, |(p.denote.coeff a : ℝ)| *
            ((p.homogenizingDegree : ℝ) * B ^ (p.homogenizingDegree - 1)) := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [← Finset.mul_sum, ← Finset.sum_mul, ← Nat.cast_sum, sum_homogeneousExponents p ha]
        _ = _ := by
          rw [← Finset.sum_mul]
          simp only [coefficientHeight, Int.cast_sum, Int.cast_abs]
          ring

private def affineLine {ι : Type*} (q v : ι → ℝ) (t : ℝ) (i : ι) : ℝ :=
  q i + t * v i

private theorem hasDerivAt_monomial_on_line {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q v : ι → ℝ) (e : ι → ℕ) (t : ℝ) :
    HasDerivAt (fun s => ∏ i, affineLine q v s i ^ e i)
      (∑ i, monomialPartial (affineLine q v t) e i * v i) t := by
  have hbase (i : ι) : HasDerivAt (fun s => affineLine q v s i) (v i) t := by
    simpa [affineLine] using ((hasDerivAt_id t).mul_const (v i)).const_add (q i)
  have hprod := HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset ι))
    (fun i _ => (hbase i).pow (e i))
  convert hprod using 1
  simp only [smul_eq_mul, monomialPartial, mul_assoc, Pi.pow_apply]

private theorem hasDerivAt_homogenizedValue_on_line (p : IntegerPolynomialCode)
    (q v : Fin (p.arity + 1) → ℝ) (t : ℝ) :
    HasDerivAt (fun s => p.homogenizedValue (affineLine q v s))
      (∑ i, p.homogenizedPartial (affineLine q v t) i * v i) t := by
  have hsum := HasDerivAt.sum (u := p.denote.support)
    (fun a _ => (hasDerivAt_monomial_on_line q v (homogeneousExponents p a) t).const_mul
      (p.denote.coeff a : ℝ))
  convert hsum using 1
  · funext s
    simpa only [Finset.sum_apply] using homogenizedValue_eq_sum p (affineLine q v s)
  · unfold homogenizedPartial
    simp_rw [Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]

/-- The displayed partials agree with one-variable derivation along coordinate lines. -/
theorem deriv_homogenizedValue_coordinate (p : IntegerPolynomialCode)
    (q : Fin (p.arity + 1) → ℝ) (i : Fin (p.arity + 1)) :
    deriv (fun t => p.homogenizedValue (fun j => q j + t * (Pi.single i (1 : ℝ) : Fin (p.arity + 1) → ℝ) j)) 0 =
      p.homogenizedPartial q i := by
  have h := (hasDerivAt_homogenizedValue_on_line p q (Pi.single i 1) 0).deriv
  have h0 : affineLine q (Pi.single i 1) 0 = q := by funext j; simp [affineLine]
  rw [h0] at h
  change deriv (fun t => p.homogenizedValue (affineLine q (Pi.single i 1) t)) 0 = _
  rw [h]
  exact dotProduct_single_one (p.homogenizedPartial q) i

/-- The segment mean-value estimate for the homogeneous polynomial. -/
theorem homogenizedValue_sub_le_meanValue (p : IntegerPolynomialCode)
    (x y : Fin (p.arity + 1) → ℝ) {B δ : ℝ}
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hx : ∀ i, |x i| ≤ B) (hy : ∀ i, |y i| ≤ B)
    (hxy : ∀ i, |y i - x i| ≤ δ) :
    |p.homogenizedValue y - p.homogenizedValue x| ≤
      (p.homogenizingDegree : ℝ) * (p.coefficientHeight : ℝ) * B ^ (p.homogenizingDegree - 1) * δ := by
  let v : Fin (p.arity + 1) → ℝ := fun i => y i - x i
  have h0 : affineLine x v 0 = x := by funext i; simp [affineLine]
  have h1 : affineLine x v 1 = y := by funext i; simp [affineLine, v]
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01'
    (fun t _ => (hasDerivAt_homogenizedValue_on_line p x v t).hasDerivWithinAt)
    (C := (p.homogenizingDegree : ℝ) * (p.coefficientHeight : ℝ) *
      B ^ (p.homogenizingDegree - 1) * δ) (fun t ht => ?_)
  · simpa only [Real.norm_eq_abs, h0, h1] using h
  · have hbox (i) : |affineLine x v t i| ≤ B := by
      rw [show affineLine x v t i = (1 - t) * x i + t * y i by unfold affineLine v; ring]
      calc
        _ ≤ |(1 - t) * x i| + |t * y i| := abs_add_le _ _
        _ ≤ (1 - t) * B + t * B := by
          rw [abs_mul, abs_mul, abs_of_nonneg (sub_nonneg.mpr ht.2.le), abs_of_nonneg ht.1]
          exact add_le_add (mul_le_mul_of_nonneg_left (hx i) (sub_nonneg.mpr ht.2.le))
            (mul_le_mul_of_nonneg_left (hy i) ht.1)
        _ = B := by ring
    rw [Real.norm_eq_abs]
    calc
      _ ≤ ∑ i, |p.homogenizedPartial (affineLine x v t) i * v i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |p.homogenizedPartial (affineLine x v t) i| * δ := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hxy i) (abs_nonneg _)
      _ ≤ _ := by
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right
          (sum_abs_homogenizedPartial_le p _ hB hbox) hδ

end ContinuousBilinear.IntegerPolynomialCode
