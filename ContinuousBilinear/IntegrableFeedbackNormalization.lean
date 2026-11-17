import ContinuousBilinear.CompilerFeedbackCodeProof
import ContinuousBilinear.IntegrableControlEquivalences

namespace ContinuousBilinear

namespace Plant

theorem globallyControllableWithIntegrableControls_clearControlDenominators (P : Plant ℚ)
    (hdrift : P.drift = Matrix.diagonal (fun i => if i.val = 0 then 1 else 0)) :
    GloballyControllableWithIntegrableControls (toReal P.clearControlDenominators) ↔
      GloballyControllableWithIntegrableControls (toReal P) := by
  rw [toReal_clearControlDenominators P hdrift]
  exact globallyControllableWithIntegrableControls_rescale_controls (toReal P)
    P.controlDenominatorScale P.controlDenominatorScale_ne_zero

end Plant

namespace FeedbackCoordinates

variable {d m : ℕ}

theorem globallyControllableWithIntegrableControls_normalizedRationalFeedback
    (K : Fin m → Matrix (Fin d) (Fin d) ℚ) (b ell : Fin d → ℚ) (h : ∑ i, ell i * b i = 1) :
    GloballyControllableWithIntegrableControls (toReal (normalizedRationalFeedback K b ell)) ↔
      GloballyControllableWithIntegrableControls (realFeedbackData K b ell).plant := by
  rw [toReal_normalizedRationalFeedback K b ell h]
  exact (globallyControllableWithIntegrableControls_conjugate
      (toReal (rationalFeedbackPlant K b ell)) (normalizingSimilarity b ell h)).trans
    (Iff.of_eq (congrArg GloballyControllableWithIntegrableControls
      (toReal_rationalFeedbackPlant K b ell)))

end FeedbackCoordinates

namespace RationalFeedbackCode

open FeedbackCoordinates

theorem integerCode_integrableControls (c : RationalFeedbackCode)
    (h : ∑ i, c.output i * c.initial i = 1) :
    GloballyControllableWithIntegrableControls (toReal c.integerCode.decode) ↔
      GloballyControllableWithIntegrableControls (realFeedbackData c.operator c.initial c.output).plant := by
  rw [integerCode_decode]
  exact (Plant.globallyControllableWithIntegrableControls_clearControlDenominators
    (normalizedRationalFeedback c.operator c.initial c.output) rfl).trans
    (globallyControllableWithIntegrableControls_normalizedRationalFeedback
      c.operator c.initial c.output h)

end RationalFeedbackCode

end ContinuousBilinear
