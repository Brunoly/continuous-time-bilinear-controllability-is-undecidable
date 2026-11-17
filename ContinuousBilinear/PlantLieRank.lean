import ContinuousBilinear.PositiveTimeInterior
import ContinuousBilinear.TransitionProducts

open scoped Matrix.Norms.Operator

namespace ContinuousBilinear

attribute [local instance] LieRing.ofAssociativeRing

/-- The Lie algebra rank condition gives a nonempty open set of transition matrices. -/
theorem interior_transitionMonoid_nonempty_of_lieSpan_eq_top (P : Plant ℝ)
    (hRank : LieSubalgebra.lieSpan ℝ (RealMatrix P.dimension)
      (Set.range (generator P)) = ⊤) :
    (interior (transitionMonoid P : Set (RealMatrix P.dimension))).Nonempty := by
  let S : Submonoid (RealMatrix P.dimension)ˣ := (transitionMonoid P).comap (Units.coeHom (RealMatrix P.dimension))
  have hExp (A : RealMatrix P.dimension) (hA : A ∈ Set.range (generator P)) (t : ℝ)
      (ht : 0 < t) :
      ∃ U ∈ S, (↑U : RealMatrix P.dimension) = NormedSpace.exp (t • A) := by
    obtain ⟨u, rfl⟩ := hA
    obtain ⟨U, hU⟩ := Matrix.isUnit_exp (t • generator P u)
    refine ⟨U, ?_, hU⟩
    change (↑U : RealMatrix P.dimension) ∈ transitionMonoid P
    rw [hU]
    exact segmentTransition_mem P t u ht.le
  have hImage : ((fun U : (RealMatrix P.dimension)ˣ => (↑U : RealMatrix P.dimension)) ''
      (S : Set (RealMatrix P.dimension)ˣ)) = transitionMonoid P := by
    ext A
    constructor
    · rintro ⟨U, hU, rfl⟩
      exact hU
    · intro hA
      obtain ⟨U, rfl⟩ := (Matrix.isUnit_iff_isUnit_det A).mpr
        (isUnit_iff_ne_zero.mpr (det_pos_of_mem_transitionMonoid P hA).ne')
      exact ⟨U, hA, rfl⟩
  have hInterior := interior_transitions_nonempty_of_lieSpan_eq_top S
    (Set.range (generator P)) hExp hRank
  exact hImage ▸ hInterior

end ContinuousBilinear
