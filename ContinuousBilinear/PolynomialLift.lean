import ContinuousBilinear.SignEncoding
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.Eval

namespace ContinuousBilinear
namespace PolynomialLift

open MvPolynomial
open scoped BigOperators Matrix

noncomputable section

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Total degree of an exponent vector, including zero exponents. -/
def monomialDegree (a : σ →₀ ℕ) : ℕ := ∑ i, a i

omit [DecidableEq σ] in
theorem sum_exponents (a : σ →₀ ℕ) :
    a.sum (fun _ n => n) = monomialDegree a :=
  Finsupp.sum_fintype _ _ (fun _ => rfl)

/-- The monomials of total degree at most the given bound. -/
def MonomialIndex (σ : Type*) [Fintype σ] (D : ℕ) :=
  {a : σ →₀ ℕ // monomialDegree a ≤ D}

instance (D : ℕ) : Fintype (MonomialIndex σ D) :=
  Fintype.ofInjective
    (fun (a : MonomialIndex σ D) i => (⟨a.val i, Nat.lt_succ_of_le
      ((Finset.single_le_sum (f := fun i => a.val i) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ i)).trans a.property)⟩ : Fin (D + 1)))
    (by
      intro a b h
      apply Subtype.ext
      ext i
      exact congrArg Fin.val (congrFun h i))

def monomialIndexEquiv (σ : Type*) [Fintype σ] [DecidableEq σ] (D : ℕ) :
    Fin (Fintype.card (MonomialIndex σ D)) ≃ MonomialIndex σ D :=
  (Fintype.equivFin _).symm

def basisMonomial (D : ℕ) (a : Fin (Fintype.card (MonomialIndex σ D))) :
    MvPolynomial σ ℤ :=
  monomial (monomialIndexEquiv σ D a).val 1

theorem totalDegree_basisMonomial (D : ℕ)
    (a : Fin (Fintype.card (MonomialIndex σ D))) :
    (basisMonomial D a : MvPolynomial σ ℤ).totalDegree ≤ D := by
  unfold basisMonomial
  refine (MvPolynomial.totalDegree_monomial_le _ (1 : ℤ)).trans ?_
  change (monomialIndexEquiv σ D a).val.sum (fun _ n => n) ≤ D
  rw [sum_exponents]
  exact (monomialIndexEquiv σ D a).property

theorem bounded_monomial_expansion (D : ℕ) (p : MvPolynomial σ ℤ)
    (hp : p.totalDegree ≤ D) :
    p = ∑ j : Fin (Fintype.card (MonomialIndex σ D)),
      p.coeff (monomialIndexEquiv σ D j).val • basisMonomial D j := by
  ext a
  simp only [coeff_sum, coeff_smul, basisMonomial, coeff_monomial, smul_eq_mul]
  by_cases ha : monomialDegree a ≤ D
  · let j := (monomialIndexEquiv σ D).symm ⟨a, ha⟩
    have hj : (monomialIndexEquiv σ D j).val = a :=
      congrArg Subtype.val ((monomialIndexEquiv σ D).apply_symm_apply ⟨a, ha⟩)
    rw [Finset.sum_eq_single j]
    · simp [hj]
    · intro k _ hk
      have hk' : (monomialIndexEquiv σ D k).val ≠ a := by
        intro e
        exact hk ((monomialIndexEquiv σ D).injective (Subtype.ext (e.trans hj.symm)))
      simp [hk']
    · simp
  · rw [show p.coeff a = 0 from by
      by_contra hne
      apply ha
      rw [← sum_exponents]
      exact (MvPolynomial.le_totalDegree (mem_support_iff.mpr hne)).trans hp]
    symm
    apply Finset.sum_eq_zero
    intro b _
    have hb : (monomialIndexEquiv σ D b).val ≠ a := by
      intro e
      exact ha (e ▸ (monomialIndexEquiv σ D b).property)
    simp [hb]

private theorem monomialDegree_sub_single (a : σ →₀ ℕ) (i : σ)
    (hi : i ∈ a.support) :
    monomialDegree (a - Finsupp.single i 1) + 1 = monomialDegree a := by
  have hle : Finsupp.single i 1 ≤ a := Finsupp.single_le_iff.mpr
    (Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi))
  unfold monomialDegree
  simp only [Finsupp.tsub_apply]
  rw [Finset.sum_tsub_distrib _ (fun j _ => hle j)]
  have hs : (∑ j, Finsupp.single i (1 : ℕ) j) = 1 := by
    simp [Finsupp.single_apply]
  rw [hs]
  apply Nat.sub_add_cancel
  exact (Finsupp.single_le_iff.mp hle).trans (Finset.single_le_sum
    (f := fun j => a j) (fun j _ => Nat.zero_le (a j)) (Finset.mem_univ i))

theorem affine_derivation_monomial_degree (f : σ → MvPolynomial σ ℤ)
    (hf : ∀ i, (f i).totalDegree ≤ 1) (a : σ →₀ ℕ) :
    (mkDerivation ℤ f (monomial a 1)).totalDegree ≤ monomialDegree a := by
  rw [mkDerivation_monomial, one_smul, Finsupp.sum]
  apply totalDegree_finsetSum_le
  intro i hi
  rw [smul_eq_mul]
  refine (totalDegree_mul _ _).trans (Nat.add_le_add ?_ (hf i)) |>.trans
    (monomialDegree_sub_single a i hi).le
  rw [← sum_exponents]
  exact totalDegree_monomial_le _ _

/-- The row indexed by a monomial records the coefficients of its derivative.
Thus this matrix is the transpose of the coefficient-column matrix of the derivation. -/
def evaluationMatrix (D : ℕ) (V : Derivation ℤ (MvPolynomial σ ℤ) (MvPolynomial σ ℤ)) :
    Matrix (Fin (Fintype.card (MonomialIndex σ D)))
      (Fin (Fintype.card (MonomialIndex σ D))) ℤ :=
  fun a b => (V (basisMonomial D a)).coeff (monomialIndexEquiv σ D b).val

theorem derivative_row_expansion (D : ℕ)
    (V : Derivation ℤ (MvPolynomial σ ℤ) (MvPolynomial σ ℤ))
    (hV : ∀ a, (V (basisMonomial D a)).totalDegree ≤ D)
    (a : Fin (Fintype.card (MonomialIndex σ D))) :
    V (basisMonomial D a) = ∑ b, evaluationMatrix D V a b • basisMonomial D b :=
  bounded_monomial_expansion D _ (hV a)

theorem commute_evaluationMatrix (D : ℕ)
    (V W : Derivation ℤ (MvPolynomial σ ℤ) (MvPolynomial σ ℤ))
    (hV : ∀ a, (V (basisMonomial D a)).totalDegree ≤ D)
    (hW : ∀ a, (W (basisMonomial D a)).totalDegree ≤ D)
    (hcomm : ∀ p, V (W p) = W (V p)) :
    Commute (evaluationMatrix D V) (evaluationMatrix D W) := by
  change evaluationMatrix D V * evaluationMatrix D W =
    evaluationMatrix D W * evaluationMatrix D V
  ext a b
  have h := congrArg (fun p : MvPolynomial σ ℤ => p.coeff (monomialIndexEquiv σ D b).val) (hcomm (basisMonomial D a))
  rw [derivative_row_expansion D W hW a, derivative_row_expansion D V hV a] at h
  simp only [map_sum, Derivation.map_smul, coeff_sum, coeff_smul, smul_eq_mul] at h
  simpa [Matrix.mul_apply, evaluationMatrix] using h.symm

end
end PolynomialLift
end ContinuousBilinear
