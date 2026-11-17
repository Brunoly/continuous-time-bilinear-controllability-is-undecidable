import ContinuousBilinear.CompilerFeedbackCodeProof
import ContinuousBilinear.FeedbackEquivalence

namespace ContinuousBilinear

namespace RationalFeedbackCode

/-- The real system represented by the rational initial vector, output, and
commuting operators of a feedback code. -/
noncomputable def realData (c : RationalFeedbackCode) :
    FeedbackData c.1 c.2.2.2.length :=
  FeedbackCoordinates.realFeedbackData c.operator c.initial c.output

theorem pairing_eq_one_of_hypotheses (c : RationalFeedbackCode) (hF : c.realData.Hypotheses) :
    ∑ i, c.output i * c.initial i = 1 := by
  have h := hF.2.1
  change (∑ i, (c.output i : ℝ) * (c.initial i : ℝ)) = 1 at h
  exact_mod_cast h

theorem commute_operator_of_hypotheses (c : RationalFeedbackCode)
    (hF : c.realData.Hypotheses) (i j : Fin c.2.2.2.length) :
    Commute (c.operator i) (c.operator j) := by
  show c.operator i * c.operator j = c.operator j * c.operator i
  have h := (hF.1 i j).eq
  change (c.operator i).map (Rat.castHom ℝ) * (c.operator j).map (Rat.castHom ℝ) =
    (c.operator j).map (Rat.castHom ℝ) * (c.operator i).map (Rat.castHom ℝ) at h
  rw [← Matrix.map_mul, ← Matrix.map_mul] at h
  ext a b
  have hp := congrFun (congrFun h a) b
  change ((c.operator i * c.operator j) a b : ℝ) =
    ((c.operator j * c.operator i) a b : ℝ) at hp
  exact_mod_cast hp

theorem integerCode_correct_of_hypotheses (c : RationalFeedbackCode)
    (hF : c.realData.Hypotheses) :
    CanonicalIntegerInstance c.integerCode ∧
      (IntegerGlobalControllability c.integerCode ↔ c.realData.HasNegativePairing) := by
  obtain ⟨hc, hEq⟩ := c.integerCode_correct (c.pairing_eq_one_of_hypotheses hF)
    (c.commute_operator_of_hypotheses hF)
  exact ⟨hc, hEq.trans (feedbackEquivalence _ _ c.realData hF)⟩

end RationalFeedbackCode

/-- Composing a computable representation of the sign encoding with canonical
integer normalization gives a reduction on every polynomial code. -/
theorem integerReduction_of_rationalFeedback
    (compile : IntegerPolynomialCode → RationalFeedbackCode) (hCompile : Computable compile)
    (hCorrect : ∀ p, (compile p).realData.Hypotheses ∧
      (p.HasIntegerRoot ↔ (compile p).realData.HasNegativePairing)) :
    Targets.IntegerReduction := by
  refine ⟨fun p => (compile p).integerCode,
    RationalFeedbackCode.computable_integerCode.comp hCompile, fun p => ?_⟩
  obtain ⟨hF, hNeg⟩ := hCorrect p
  obtain ⟨hc, hEq⟩ := (compile p).integerCode_correct_of_hypotheses hF
  exact ⟨hc, hNeg.trans hEq.symm⟩

end ContinuousBilinear
