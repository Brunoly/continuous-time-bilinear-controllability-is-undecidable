import ContinuousBilinear.FeedbackEquivalence
import ContinuousBilinear.PolynomialLiftQuotientFeedback
import ContinuousBilinear.CompilerFeedbackNormalizationProof

namespace ContinuousBilinear

/-- The reduction's correctness for each source instance, including every
integer output restriction. Effectiveness of a uniform selection of outputs
is a separate obligation. -/
theorem exists_canonicalIntegerInstance_iff_hasIntegerRoot (p : IntegerPolynomialCode) :
    ∃ c : IntegerPlantCode, CanonicalIntegerInstance c ∧
      (p.HasIntegerRoot ↔ IntegerGlobalControllability c) := by
  obtain ⟨d, m, K, b, ell, hF, hNeg⟩ := PolynomialLift.exists_rational_feedback p
  let F := FeedbackCoordinates.realFeedbackData K b ell
  change F.Hypotheses at hF
  change F.HasNegativePairing ↔ p.HasIntegerRoot at hNeg
  have hPair : ∑ i, ell i * b i = (1 : ℚ) := by
    have hReal := hF.2.1
    change (∑ i, (ell i : ℝ) * (b i : ℝ)) = 1 at hReal
    exact_mod_cast hReal
  have hCommute (i j : Fin m) : Commute (K i) (K j) := by
    show K i * K j = K j * K i
    have h := (hF.1 i j).eq
    change (K i).map (Rat.castHom ℝ) * (K j).map (Rat.castHom ℝ) =
      (K j).map (Rat.castHom ℝ) * (K i).map (Rat.castHom ℝ) at h
    rw [← Matrix.map_mul, ← Matrix.map_mul] at h
    ext a b
    have hp := congrFun (congrFun h a) b
    change ((K i * K j) a b : ℝ) = ((K j * K i) a b : ℝ) at hp
    exact_mod_cast hp
  obtain ⟨c, hc, heq⟩ :=
    FeedbackCoordinates.exists_integerPlantCode_of_rationalFeedback K b ell hPair hCommute
  exact ⟨c, hc, hNeg.symm.trans ((feedbackEquivalence d m F hF).symm.trans heq.symm)⟩

end ContinuousBilinear
