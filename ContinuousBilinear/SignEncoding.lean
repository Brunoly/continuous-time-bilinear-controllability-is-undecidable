import ContinuousBilinear.Encoding
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

namespace ContinuousBilinear

namespace IntegerPolynomialCode

noncomputable def homogenizingDegree (p : IntegerPolynomialCode) : ℕ :=
  max 1 p.denote.totalDegree

noncomputable def coefficientHeight (p : IntegerPolynomialCode) : ℤ :=
  ∑ a ∈ p.denote.support, |p.denote.coeff a|

noncomputable def signScale (p : IntegerPolynomialCode) : ℤ :=
  2 ^ (p.homogenizingDegree + 1) * (p.homogenizingDegree : ℤ) * (p.coefficientHeight + 1)

noncomputable def homogenizedValue (p : IntegerPolynomialCode)
    (q : Fin (p.arity + 1) → ℝ) : ℝ :=
  ∑ a ∈ p.denote.support, (p.denote.coeff a : ℝ) *
    q 0 ^ (p.homogenizingDegree - a.sum (fun _ e => e)) *
    ∏ i : Fin p.arity, q i.succ ^ a i

noncomputable def signPolynomialValue (p : IntegerPolynomialCode)
    (q osc : Fin (p.arity + 1) → ℝ) (a : ℝ) : ℝ :=
  p.homogenizedValue q ^ 2 + (p.signScale : ℝ) ^ 2 *
    (1 + ∑ i, q i ^ 2) ^ (p.homogenizingDegree - 1) *
    ((∑ i, osc i ^ 2) + ((q 0 - 3) * (4 - q 0) - a ^ 2) ^ 2) - 1

end IntegerPolynomialCode

namespace Targets

/-- The quantitative sign-encoding lemma, with the manuscript's exact constants. -/
def SignEncoding : Prop :=
  ∀ p : IntegerPolynomialCode,
    (∃ (q : Fin (p.arity + 1) → ℝ) (a : ℝ),
      p.signPolynomialValue q (fun i => Real.sin (q i)) a < 0) ↔ p.HasIntegerRoot

end Targets
end ContinuousBilinear
