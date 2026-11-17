import ContinuousBilinear.ConjugationDerivative
import ContinuousBilinear.LieSpanInvariance
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Set

attribute [local instance] LieRing.ofAssociativeRing

namespace ContinuousBilinear

/-- The adjoint orbit of the generators under positive-time products spans the
ambient algebra when the generators have full Lie span. -/
theorem span_conjugates_eq_top_of_lieSpan_eq_top {R : Type*}
    [NormedRing R] [NormedAlgebra ℝ R] [NormedAlgebra ℚ R] [CompleteSpace R] [FiniteDimensional ℝ R]
    (S : Submonoid Rˣ) (generators : Set R)
    (hExp : ∀ a ∈ generators, ∀ t : ℝ, 0 < t →
      ∃ u ∈ S, (↑u : R) = NormedSpace.exp (t • a))
    (hLie : LieSubalgebra.lieSpan ℝ R generators = ⊤) :
    Submodule.span ℝ {z : R | ∃ u ∈ S, ∃ a ∈ generators,
      z = (↑u : R) * a * ↑u⁻¹} = ⊤ := by
  let orbit : Set R := {z | ∃ u ∈ S, ∃ a ∈ generators, z = (↑u : R) * a * ↑u⁻¹}
  let L := Submodule.span ℝ orbit
  have hGen : generators ⊆ L := by
    intro a ha
    exact Submodule.subset_span ⟨1, S.one_mem, a, ha, by simp⟩
  have hInvariant (u : Rˣ) (hu : u ∈ S) {x : R} (hx : x ∈ L) :
      (↑u : R) * x * ↑u⁻¹ ∈ L := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, hv, a, ha, rfl⟩ := hx
      exact Submodule.subset_span ⟨u * v, S.mul_mem hu hv, a, ha, by simp [mul_assoc]⟩
    | zero => simp
    | add x y _ _ hx hy => simpa [mul_add, add_mul] using L.add_mem hx hy
    | smul c x _ hx =>
      simpa [mul_smul_comm, smul_mul_assoc] using L.smul_mem c hx
  have hAd (a : R) (ha : a ∈ generators) (x : R) (hx : x ∈ L) : ⁅a, x⁆ ∈ L := by
    change a * x - x * a ∈ L
    apply commutator_mem_of_exp_conjugation_mem a L L.closed_of_finiteDimensional _ hx
    intro t ht y hy
    obtain ⟨u, hu, hval⟩ := hExp a ha t ht
    have hneg : NormedSpace.exp (t • -a) = (↑u⁻¹ : R) := by
      rw [smul_neg, ← Ring.inverse_exp, ← hval, Ring.inverse_unit]
    rw [← hval, hneg]
    exact hInvariant u hu hy
  have hle := lieSpan_le_of_lie_mem generators L hGen hAd
  rw [hLie] at hle
  exact top_unique hle

end ContinuousBilinear
