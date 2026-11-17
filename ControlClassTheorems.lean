import MainTheorems

/-! Control-class equivalence for the feedback family and the integer reduction.
The general matrix definitions and analytic equivalences are in MainTheorems.
The feedback hypotheses are defined in ContinuousBilinear/Feedback.lean. -/

namespace ContinuousBilinear

/-- Under the feedback hypotheses, both control classes give the same
answer to global controllability. -/
theorem feedbackControlClasses_iff {d m : ℕ} (F : FeedbackData d m)
    (hF : F.Hypotheses) :
    BilinearControllability.GloballyControllable F.plant.drift F.plant.control ↔
      BilinearControllability.GloballyControllableWithIntegrableControls
        F.plant.drift F.plant.control := by
  change BilinearControllability.GloballyControllable F.plant.drift F.plant.control ↔
    GloballyControllableWithIntegrableControls F.plant
  constructor
  · exact BilinearControllability.GloballyControllable.integrableControls
  · intro h
    have hPC := (feedbackEquivalence d m F hF).mpr
      ((feedbackEquivalenceWithIntegrableControls F hF).mpr h)
    intro x y hx hy
    obtain ⟨M, hM, hxy⟩ := hPC x y hx hy
    obtain ⟨steps, hpos, rfl⟩ := (transitionProductSemantics F.plant M).mp hM
    exact ⟨steps, hpos, hxy⟩

/-- A single computable reduction gives equivalent control problems for
both classes on every output, preserving the integer-root problem. -/
theorem exists_reduction_with_equivalent_controlClasses :
    ∃ f : IntegerPolynomialCode → IntegerPlantCode,
      Computable f ∧ ∀ p,
        CanonicalIntegerInstance (f p) ∧
        (p.HasIntegerRoot ↔ IntegerGlobalControllability (f p)) ∧
        (IntegerGlobalControllability (f p) ↔
          GloballyControllableWithIntegrableControls (toReal (f p).decode)) := by
  obtain ⟨f, hf, h⟩ := integerReductionWithIntegrableControls
  refine ⟨f, hf, fun p => ?_⟩
  obtain ⟨hc, hPC, hL1⟩ := h p
  exact ⟨hc, hPC, hPC.symm.trans hL1⟩

end ContinuousBilinear

#print axioms ContinuousBilinear.feedbackControlClasses_iff
#print axioms ContinuousBilinear.exists_reduction_with_equivalent_controlClasses
