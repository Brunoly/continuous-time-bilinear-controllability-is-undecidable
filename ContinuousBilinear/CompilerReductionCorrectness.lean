import ContinuousBilinear.CompilerReduction
import ContinuousBilinear.CompilerWordAgreementProof
import ContinuousBilinear.PolynomialLiftComputableRationalCorrectness
import ContinuousBilinear.PolynomialLiftQuotientFeedback

namespace ContinuousBilinear.RationalFeedbackCode

open PolynomialLift
open scoped Matrix.Norms.Operator

private theorem coordinateOperators_representationWithAlphabet (c : RationalFeedbackCode)
    {m : ℕ} (hm : m = c.2.2.2.length) (i : Fin m) :
    (c.representationWithAlphabet hm).coordinateOperators (Pi.basisFun ℚ (Fin c.1)) i =
      c.operator (Fin.cast hm i) := by
  unfold LinearRepresentation.coordinateOperators
  rw [LinearMap.toMatrix_eq_toMatrix']
  change LinearMap.toMatrix' (Matrix.mulVecLin (c.operator (Fin.cast hm i))) = _
  rw [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']

private theorem representation_output_basis (c : RationalFeedbackCode) (i : Fin c.1) :
    c.representation.output ((Pi.basisFun ℚ (Fin c.1)) i) = c.output i := by
  simp [representation, Pi.basisFun_apply]

theorem realData_hypotheses_of_minimal (c : RationalFeedbackCode)
    (hcomm : ∀ i j, Commute (c.operator i) (c.operator j))
    (hinit : ∑ i, c.output i * c.initial i = 1)
    (hReach : c.representation.reachable = ⊤)
    (hObs : Submodule.span ℚ (Set.range fun w => c.representation.output.comp
      (c.representation.wordAction w)) = ⊤) :
    c.realData.Hypotheses := by
  let B := Pi.basisFun ℚ (Fin c.1)
  have hRep (i j : Fin c.2.2.2.length) :
      Commute (c.representation.operator i) (c.representation.operator j) := by
    show (c.operator i).mulVecLin.comp (c.operator j).mulVecLin =
      (c.operator j).mulVecLin.comp (c.operator i).mulVecLin
    rw [← Matrix.mulVecLin_mul, ← Matrix.mulVecLin_mul, (hcomm i j).eq]
  have h := c.representation.feedbackData_hypotheses B (Equiv.refl _) hRep hinit hReach hObs
  have hEq : c.representation.feedbackData B (Equiv.refl _) = c.realData := by
    have hK : (c.representation.feedbackData B (Equiv.refl _)).K = c.realData.K := by
      funext i
      change ((c.representationWithAlphabet rfl).coordinateOperators B i).map (Rat.castHom ℝ) =
        (c.operator i).map (Rat.castHom ℝ)
      rw [coordinateOperators_representationWithAlphabet]
      rfl
    have hb : (c.representation.feedbackData B (Equiv.refl _)).b = c.realData.b := by
      funext i
      simp [B, LinearRepresentation.feedbackData, LinearRepresentation.realCoordinates,
        representation, realData, FeedbackCoordinates.realFeedbackData]
    have hOut : (c.representation.feedbackData B (Equiv.refl _)).ell = c.realData.ell := by
      funext i
      change (c.representation.output (B i) : ℝ) = (c.output i : ℝ)
      rw [representation_output_basis]
    exact (congrArg₂
        (fun K b => FeedbackData.mk K b (c.representation.feedbackData B (Equiv.refl _)).ell)
        hK hb).trans
      (congrArg (FeedbackData.mk c.realData.K c.realData.b) hOut)
  exact hEq ▸ h

private theorem exponentialCoefficient_eq_pairing (c : RationalFeedbackCode)
    {m : ℕ} (hm : m = c.2.2.2.length) (u : Fin m → ℝ) :
    (c.representationWithAlphabet hm).exponentialCoefficient (Pi.basisFun ℚ (Fin c.1)) u =
      c.realData.pairing ((c.realData.orbitMatrix (u ∘ Fin.cast hm.symm)).mulVec c.realData.b) := by
  unfold LinearRepresentation.exponentialCoefficient LinearRepresentation.realOutput
    FeedbackData.pairing FeedbackData.orbitMatrix
  have hp :
      realPencil ((c.representationWithAlphabet hm).coordinateOperators (Pi.basisFun ℚ (Fin c.1))) u =
      ∑ i, (u ∘ Fin.cast hm.symm) i • c.realData.K i := by
    unfold realPencil
    refine Fintype.sum_equiv (finCongr hm) _ _ (fun i => ?_)
    rw [coordinateOperators_representationWithAlphabet]
    change u i • (c.operator (Fin.cast hm i)).map (Rat.castHom ℝ) =
      u (Fin.cast hm.symm (Fin.cast hm i)) •
        (c.operator (Fin.cast hm i)).map (Rat.castHom ℝ)
    simp
  rw [hp]
  apply Finset.sum_congr rfl
  intro j _
  change (c.representation.output ((Pi.basisFun ℚ (Fin c.1)) j) : ℝ) * _ =
    (c.output j : ℝ) * _
  rw [representation_output_basis]
  rfl

private theorem exists_negative_exponentialCoefficient_iff (c : RationalFeedbackCode)
    {m : ℕ} (hm : m = c.2.2.2.length) :
    (∃ u, (c.representationWithAlphabet hm).exponentialCoefficient
      (Pi.basisFun ℚ (Fin c.1)) u < 0) ↔ c.realData.HasNegativePairing := by
  simp_rw [exponentialCoefficient_eq_pairing c hm]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u ∘ Fin.cast hm.symm, hu⟩
  · rintro ⟨v, hv⟩
    refine ⟨v ∘ Fin.cast hm, ?_⟩
    have he : (v ∘ Fin.cast hm) ∘ Fin.cast hm.symm = v := by
      funext i
      simp [Function.comp_def]
    rwa [he]

/-- A finite agreement test on the rational word coefficients preserves the
existence of a negative real exponential coefficient. -/
theorem hasNegativePairing_iff_of_wordOutputsAgree (c e : RationalFeedbackCode)
    (h : wordOutputsAgree (c, e)) :
    c.realData.HasNegativePairing ↔ e.realData.HasNegativePairing := by
  rw [← exists_negative_exponentialCoefficient_iff c rfl,
    ← exists_negative_exponentialCoefficient_iff e h.1]
  apply exists_congr
  intro u
  rw [← exponentialCoefficient_eq_of_wordOutputsAgree c e h u]
  rfl

theorem compileRationalLift_hasNegativePairing_iff (p : IntegerPolynomialCode) :
    (compileRationalLift p).realData.HasNegativePairing ↔ p.HasIntegerRoot :=
  compileRationalLift_negative_iff p

private theorem wordOutput_nil_eq_pairing (c : RationalFeedbackCode) :
    c.wordOutput [] = ∑ i, c.output i * c.initial i := by
  simpa [representation, LinearRepresentation.wordAction, dotProduct] using
    c.wordOutput_eq ([] : List (Fin c.2.2.2.length))

/-- Correctness of a minimal rational realization of the compiled polynomial
lift, verified using bounded word agreement. -/
theorem correct_of_wordOutputsAgree (p : IntegerPolynomialCode) (c : RationalFeedbackCode)
    (hcomm : ∀ i j, Commute (c.operator i) (c.operator j))
    (hReach : c.representation.reachable = ⊤)
    (hObs : Submodule.span ℚ (Set.range fun w => c.representation.output.comp
      (c.representation.wordAction w)) = ⊤)
    (hAgree : wordOutputsAgree (compileRationalLift p, c)) :
    c.realData.Hypotheses ∧ (p.HasIntegerRoot ↔ c.realData.HasNegativePairing) := by
  have hNil := hAgree.2 []
    ((mem_wordsUpTo _ _ _).mpr ⟨by simp, by simp⟩)
  rw [wordOutput_nil_eq_pairing, wordOutput_nil_eq_pairing,
    compileRationalLift_initial_coefficient] at hNil
  exact ⟨c.realData_hypotheses_of_minimal hcomm hNil.symm hReach hObs,
    (compileRationalLift_hasNegativePairing_iff p).symm.trans
      (hasNegativePairing_iff_of_wordOutputsAgree _ c hAgree)⟩

end ContinuousBilinear.RationalFeedbackCode
