import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

open Filter Topology

namespace ContinuousBilinear

/-- A locally realized endpoint map with a surjective strict derivative produces
an interior point of the realizable set. -/
theorem mem_interior_of_surjective_derivative
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {S : Set F} (endpoint : E → F) (a : E) (D : E →L[ℝ] F)
    (hDeriv : HasStrictFDerivAt endpoint D a) (hSurj : D.range = ⊤)
    (hRealizable : ∀ᶠ x in 𝓝 a, endpoint x ∈ S) :
    endpoint a ∈ interior S := by
  apply mem_interior_iff_mem_nhds.mpr
  exact (hDeriv.map_nhds_eq_of_surj hSurj).ge hRealizable

end ContinuousBilinear
