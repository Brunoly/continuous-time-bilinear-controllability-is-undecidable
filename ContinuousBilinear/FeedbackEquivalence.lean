import ContinuousBilinear.FeedbackProof
import ContinuousBilinear.FeedbackLieRank
import ContinuousBilinear.FeedbackDensityProof
import ContinuousBilinear.MatrixSemigroupExactness
import ContinuousBilinear.PositiveDeterminantAction

namespace ContinuousBilinear

theorem feedbackExactTransitions : Targets.FeedbackExactTransitions := by
  intro d m F hF hneg M
  refine ⟨det_pos_of_mem_transitionMonoid F.plant, fun hM => ?_⟩
  apply mem_of_pos_det_of_mem_closure_of_interior (transitionMonoid F.plant)
    (fun _ h => det_pos_of_mem_transitionMonoid F.plant h) _ _ hM
  · intro A hA
    exact F.positive_det_mem_topologicalClosure hF hneg hA
  · exact interior_transitionMonoid_nonempty_of_lieSpan_eq_top F.plant
      (F.lieSpan_generator_eq_top hF)

theorem feedbackEquivalence : Targets.FeedbackEquivalence := by
  intro d m F hF
  refine ⟨F.hasNegativePairing_of_globallyControllable hF.1, ?_⟩
  intro hneg x y hx hy
  have hd : 2 ≤ d + 1 := by
    cases d with
    | zero =>
      have hPair := hF.2.1
      simp [FeedbackData.pairing] at hPair
    | succ k => omega
  obtain ⟨M, hM, hxy⟩ := exists_pos_det_mulVec_eq hd x y hx hy
  exact ⟨M, (feedbackExactTransitions d m F hF hneg M).mpr hM, hxy⟩

end ContinuousBilinear
