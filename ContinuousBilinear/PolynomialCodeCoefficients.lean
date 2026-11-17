import ContinuousBilinear.SignEncoding

namespace ContinuousBilinear.IntegerPolynomialCode

open MvPolynomial

private noncomputable def exponentVector (n : ℕ) (exponents : List ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => exponents.getD i.val 0)

/-- Compute a coefficient by summing all terms with the same padded exponent vector. -/
def coefficient (p : IntegerPolynomialCode) (exponents : List ℕ) : ℤ :=
  (p.map fun term =>
    if (List.range p.arity).all (fun i => term.2.getD i 0 == exponents.getD i 0)
    then term.1 else 0).sum

theorem coefficient_eq_coeff (p : IntegerPolynomialCode) (exponents : List ℕ) :
    coefficient p exponents = p.denote.coeff (exponentVector p.arity exponents) := by
  let a := exponentVector p.arity exponents
  have hEq (term : ℤ × List ℕ) :
      (List.range p.arity).all (fun i => term.2.getD i 0 == exponents.getD i 0) = true ↔
        exponentVector p.arity term.2 = a := by
    simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
    constructor
    · intro h
      ext i
      exact h i.val i.isLt
    · intro h i hi
      exact DFunLike.congr_fun h ⟨i, hi⟩
  have hTerm (term : ℤ × List ℕ) :
      MvPolynomial.C term.1 * (∏ i : Fin p.arity, MvPolynomial.X i ^ term.2.getD i.val 0) =
        MvPolynomial.monomial (exponentVector p.arity term.2) term.1 := by
    rw [prod_X_pow]
    have hv : Finsupp.indicator (Finset.univ : Finset (Fin p.arity))
        (fun i _ => term.2.getD i.val 0) = exponentVector p.arity term.2 := by
      ext i
      simp [Finsupp.indicator, exponentVector]
    rw [hv, C_mul_monomial, mul_one]
  change _ = lcoeff ℤ a _
  rw [denote, map_list_sum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro term _
  simp only [Function.comp_apply, hTerm, lcoeff_apply, coeff_monomial]
  by_cases h : exponentVector p.arity term.2 = a
  · simp only [(hEq term).mpr h, if_true, h]
  · have h' : (List.range p.arity).all (fun i => term.2.getD i 0 == exponents.getD i 0) = false :=
      Bool.eq_false_iff.mpr fun htrue => h ((hEq term).mp htrue)
    simp only [h', Bool.false_eq_true, if_false, h, Ne.symm h]

end ContinuousBilinear.IntegerPolynomialCode
