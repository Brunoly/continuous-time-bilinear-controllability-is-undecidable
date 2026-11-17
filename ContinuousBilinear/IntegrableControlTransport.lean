import ContinuousBilinear.Semantics

open MeasureTheory

namespace ContinuousBilinear

/-- Transport a finite-horizon integral solution by linear changes of state and input. -/
theorem integrableControlReachable_map
    (P Q : Plant ℝ) (E : State P.dimension ≃L[ℝ] State Q.dimension)
    (U : (Fin P.controls → ℝ) →L[ℝ] (Fin Q.controls → ℝ))
    (hField : ∀ v z, E ((generator P v).mulVec z) = (generator Q (U v)).mulVec (E z))
    {x y : State P.dimension} (h : IntegrableControlReachable P x y) :
    IntegrableControlReachable Q (E x) (E y) := by
  obtain ⟨T, u, z, hT, hu, hz, hx, hy, hEq⟩ := h
  refine ⟨T, U ∘ u, E ∘ z, hT, U.integrable_comp hu, E.continuous.comp_continuousOn hz,
    congrArg E hx, congrArg E hy, ?_⟩
  intro t ht
  have hIntegral (f : ℝ → State P.dimension) :
      (∫ s in (0 : ℝ)..t, E (f s)) = E (∫ s in (0 : ℝ)..t, f s) := by
    simp_rw [intervalIntegral, E.integral_comp_comm, E.map_sub]
  change E (z t) = E x + ∫ s in (0 : ℝ)..t,
    (generator Q (U (u s))).mulVec (E (z s))
  simp_rw [← hField]
  rw [hIntegral, ← E.map_add, hEq t ht]

end ContinuousBilinear
