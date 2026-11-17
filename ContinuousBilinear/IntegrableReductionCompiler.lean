import ContinuousBilinear.CompilerReductionCorrectness
import ContinuousBilinear.CompilerMinimalEncodingProof
import ContinuousBilinear.PolynomialLiftComputableCommutation
import ContinuousBilinear.IntegrableFeedbackNormalization
import ContinuousBilinear.IntegrableFeedbackEquivalence

namespace ContinuousBilinear

/-- The same canonical integer compiler preserves the answer for
piecewise-constant and for locally integrable controls. -/
theorem integerReductionWithIntegrableControls_of_rationalFeedback
    (compile : IntegerPolynomialCode → RationalFeedbackCode) (hCompile : Computable compile)
    (hCorrect : ∀ p, (compile p).realData.Hypotheses ∧
      (p.HasIntegerRoot ↔ (compile p).realData.HasNegativePairing)) :
    Targets.IntegerReductionWithIntegrableControls := by
  refine ⟨fun p => (compile p).integerCode,
    RationalFeedbackCode.computable_integerCode.comp hCompile, fun p => ?_⟩
  obtain ⟨hF, hNeg⟩ := hCorrect p
  obtain ⟨hc, hEq⟩ := (compile p).integerCode_correct_of_hypotheses hF
  have hNormalize := (compile p).integerCode_integrableControls
    ((compile p).pairing_eq_one_of_hypotheses hF)
  refine ⟨hc, hNeg.trans hEq.symm, ?_⟩
  exact hNeg.trans ((feedbackEquivalenceWithIntegrableControls (compile p).realData hF).trans
    hNormalize.symm)

/-- Every polynomial has a canonical integer plant giving the same answer
for both control classes. The witness is obtained using the rational
reachable and observable quotient. -/
theorem exists_canonicalIntegerInstance_withIntegrableControls_iff_hasIntegerRoot
    (p : IntegerPolynomialCode) :
    ∃ c : IntegerPlantCode, CanonicalIntegerInstance c ∧
      (p.HasIntegerRoot ↔ IntegerGlobalControllability c) ∧
      (p.HasIntegerRoot ↔ GloballyControllableWithIntegrableControls (toReal c.decode)) := by
  obtain ⟨c, hAgree, hComm, hReach, hObs⟩ :=
    RationalFeedbackCode.exists_minimal_wordOutputsAgree
      (PolynomialLift.compileRationalLift p) (PolynomialLift.compileRationalLift_operators_commute p)
  obtain ⟨hF, hNeg⟩ := c.correct_of_wordOutputsAgree p hComm hReach hObs hAgree
  obtain ⟨hc, hEq⟩ := c.integerCode_correct_of_hypotheses hF
  have hNormalize := c.integerCode_integrableControls (c.pairing_eq_one_of_hypotheses hF)
  refine ⟨c.integerCode, hc, hNeg.trans hEq.symm, ?_⟩
  exact hNeg.trans ((feedbackEquivalenceWithIntegrableControls c.realData hF).trans
    hNormalize.symm)

end ContinuousBilinear
