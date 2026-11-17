import ContinuousBilinear.CompilerGaussianQuotient
import ContinuousBilinear.IntegrableReductionCompiler
import ContinuousBilinear.IntegrableReductionConsequences

namespace ContinuousBilinear

open PolynomialLift

/-- The rational minimal realization obtained by elimination of the bounded
observation table of the polynomial lift. -/
def compileMinimalFeedback (p : IntegerPolynomialCode) : RationalFeedbackCode :=
  (compileRationalLift p).gaussianQuotient

theorem computable_compileMinimalFeedback : Computable compileMinimalFeedback :=
  RationalFeedbackCode.computable_gaussianQuotient.comp computable_compileRationalLift

theorem compileMinimalFeedback_correct (p : IntegerPolynomialCode) :
    (compileMinimalFeedback p).realData.Hypotheses ∧
      (p.HasIntegerRoot ↔ (compileMinimalFeedback p).realData.HasNegativePairing) := by
  obtain ⟨hAgree, hComm, hReach, hObs⟩ :=
    (compileRationalLift p).gaussianQuotient_correct (compileRationalLift_operators_commute p)
  exact (compileMinimalFeedback p).correct_of_wordOutputsAgree p hComm hReach hObs hAgree

/-- One computable compiler works for both piecewise-constant and locally
integrable controls. -/
theorem integerReductionWithIntegrableControls : Targets.IntegerReductionWithIntegrableControls :=
  integerReductionWithIntegrableControls_of_rationalFeedback compileMinimalFeedback
    computable_compileMinimalFeedback compileMinimalFeedback_correct

theorem integerReduction : Targets.IntegerReduction := by
  obtain ⟨f, hf, h⟩ := integerReductionWithIntegrableControls
  exact ⟨f, hf, fun p => ⟨(h p).1, (h p).2.1⟩⟩

end ContinuousBilinear
