import ContinuousBilinear.TransitionProducts

namespace ContinuousBilinear

/-- Rescaling individual control matrices by nonzero constants leaves the set of
constant generators, and hence all finite transitions, unchanged. -/
theorem transitionMonoid_rescale_controls (P : Plant ℝ)
    (scale : Fin P.controls → ℝ) (hscale : ∀ i, scale i ≠ 0) :
    transitionMonoid {P with control := fun i => scale i • P.control i} =
      transitionMonoid P := by
  unfold transitionMonoid
  congr 1
  ext M
  constructor
  · rintro ⟨t, u, ht, hM⟩
    use t, (fun i => u i * scale i), ht
    simpa [segmentTransition, generator, smul_smul] using hM
  · rintro ⟨t, u, ht, hM⟩
    use t, (fun i => u i / scale i), ht
    have hmul (i : Fin P.controls) : u i / scale i * scale i = u i :=
      div_mul_cancel₀ _ (hscale i)
    simpa [segmentTransition, generator, smul_smul, hmul] using hM

theorem globallyControllable_rescale_controls (P : Plant ℝ)
    (scale : Fin P.controls → ℝ) (hscale : ∀ i, scale i ≠ 0) :
    GloballyControllable {P with control := fun i => scale i • P.control i} ↔
      GloballyControllable P := by
  unfold GloballyControllable
  simp only [transitionMonoid_rescale_controls P scale hscale]

end ContinuousBilinear
