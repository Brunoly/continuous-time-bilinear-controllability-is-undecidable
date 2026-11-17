import Mathlib.Topology.Algebra.Group.Basic

namespace Submonoid

/-- A dense submonoid of a topological group is the whole group if it contains a
nonempty open subset. -/
theorem eq_top_of_dense_of_exists_open_subset {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (S : Submonoid G)
    (hDense : Dense (S : Set G)) {O : Set G} (hOpen : IsOpen O)
    (hNonempty : O.Nonempty) (hSubset : O ⊆ (S : Set G)) : S = ⊤ := by
  apply top_unique
  intro g _
  let U := (fun o : G => g * o⁻¹) '' O
  have hU : IsOpen U := ((isOpenMap_mul_left g).comp (isOpenMap_inv G)) O hOpen
  have hUne : U.Nonempty := hNonempty.image _
  obtain ⟨s, hs, hsU⟩ := hDense.exists_mem_open hU hUne
  obtain ⟨o, ho, rfl⟩ := hsU
  have h := S.mul_mem hs (hSubset ho)
  simpa [mul_assoc] using h

end Submonoid
