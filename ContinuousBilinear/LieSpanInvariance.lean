import Mathlib.Algebra.Lie.Subalgebra

namespace ContinuousBilinear

/-- A subspace containing the generators and invariant under their adjoint
actions contains the Lie algebra they generate. -/
theorem lieSpan_le_of_lie_mem {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (S : Set L) (W : Submodule R L) (hGen : S ⊆ W)
    (hInvariant : ∀ a ∈ S, ∀ x ∈ W, ⁅a, x⁆ ∈ W) :
    (LieSubalgebra.lieSpan R L S).toSubmodule ≤ W := by
  let N : LieSubalgebra R L :=
    { carrier := {a | a ∈ W ∧ ∀ x ∈ W, ⁅a, x⁆ ∈ W}
      zero_mem' := ⟨W.zero_mem, fun x _ => by simp⟩
      add_mem' := fun ha hb => ⟨W.add_mem ha.1 hb.1, fun x hx => by
        rw [add_lie]
        exact W.add_mem (ha.2 x hx) (hb.2 x hx)⟩
      smul_mem' := fun t a ha => ⟨W.smul_mem t ha.1, fun x hx => by
        rw [smul_lie]
        exact W.smul_mem t (ha.2 x hx)⟩
      lie_mem' := fun {a b} ha hb => ⟨ha.2 b hb.1, fun x hx => by
        have hJacobi : ⁅⁅a, b⁆, x⁆ = ⁅a, ⁅b, x⁆⁆ - ⁅b, ⁅a, x⁆⁆ :=
          eq_sub_of_add_eq (leibniz_lie a b x).symm
        rw [hJacobi]
        exact W.sub_mem (ha.2 _ (hb.2 x hx)) (hb.2 _ (ha.2 x hx))⟩ }
  have hN : LieSubalgebra.lieSpan R L S ≤ N :=
    LieSubalgebra.lieSpan_le.mpr fun a ha => ⟨hGen ha, hInvariant a ha⟩
  exact fun a ha => (show a ∈ W ∧ ∀ x ∈ W, ⁅a, x⁆ ∈ W from hN ha).1

end ContinuousBilinear
