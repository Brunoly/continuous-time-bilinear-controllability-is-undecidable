import ContinuousBilinear.FeedbackEquivalence
import ContinuousBilinear.IntegrableControlConeApproximation

namespace ContinuousBilinear

theorem feedbackEquivalenceWithIntegrableControls {d m : ℕ} (F : FeedbackData d m)
    (hF : F.Hypotheses) :
    F.HasNegativePairing ↔ GloballyControllableWithIntegrableControls F.plant := by
  exact ⟨fun h => ((feedbackEquivalence d m F hF).mpr h).integrableControls,
    F.hasNegativePairing_of_integrableControls hF.1⟩

end ContinuousBilinear
