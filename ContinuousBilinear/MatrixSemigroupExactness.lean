import ContinuousBilinear.TransitionProducts
import Mathlib.Topology.Instances.Matrix

open Set Filter Topology

namespace ContinuousBilinear

/-- Exactness in the ambient matrix space. A semigroup of positive-determinant
matrices that is dense in that region and has interior contains the whole region. -/
theorem mem_of_pos_det_of_mem_closure_of_interior {n : ℕ} (S : Submonoid (RealMatrix n))
    (hPos : ∀ A ∈ S, 0 < Matrix.det A)
    (hDense : ∀ A : RealMatrix n, 0 < A.det → A ∈ closure (S : Set (RealMatrix n)))
    (hInterior : (interior (S : Set (RealMatrix n))).Nonempty)
    {G : RealMatrix n} (hG : 0 < G.det) : G ∈ S := by
  obtain ⟨O, hO⟩ := hInterior
  have hOdet := hPos O (interior_subset hO)
  obtain ⟨U, rfl⟩ := (Matrix.isUnit_iff_isUnit_det O).mpr (isUnit_iff_ne_zero.mpr hOdet.ne')
  obtain ⟨V, rfl⟩ := (Matrix.isUnit_iff_isUnit_det G).mpr (isUnit_iff_ne_zero.mpr hG.ne')
  let W := V * U⁻¹
  have hUinv : 0 < (↑U⁻¹ : RealMatrix n).det := by
    have hprod : (↑U⁻¹ : RealMatrix n).det * (↑U : RealMatrix n).det = 1 := by
      rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one]
    exact pos_of_mul_pos_left (hprod ▸ zero_lt_one) hOdet.le
  have hW : 0 < (↑W : RealMatrix n).det := by
    change (0 : ℝ) < Matrix.det ((↑V : RealMatrix n) * (↑U⁻¹ : RealMatrix n))
    rw [Matrix.det_mul]
    exact mul_pos hG hUinv
  let f (A : RealMatrix n) := A⁻¹ * (↑V : RealMatrix n)
  have hf : ContinuousAt f (↑W : RealMatrix n) := by
    have hi : ContinuousAt (Ring.inverse : ℝ → ℝ) (↑W : RealMatrix n).det := by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_id.inv₀ hW.ne'
    exact (continuousAt_matrix_inv _ hi).mul continuousAt_const
  have hfW : f ↑W = (↑U : RealMatrix n) := by
    rw [show f ↑W = (↑W : RealMatrix n)⁻¹ * ↑V from rfl, ← Matrix.coe_units_inv]
    change (↑((V * U⁻¹)⁻¹ * V) : RealMatrix n) = ↑U
    congr 1
    group
  have hNearby : {A | f A ∈ interior (S : Set (RealMatrix n))} ∈ 𝓝 (↑W : RealMatrix n) :=
    hf (isOpen_interior.mem_nhds (hfW.symm ▸ hO))
  have hFreq := mem_closure_iff_frequently.mp (hDense ↑W hW)
  obtain ⟨A, hAS, hfA⟩ := (hFreq.and_eventually hNearby).exists
  have hUnit : IsUnit A :=
    (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr (hPos A hAS).ne')
  obtain ⟨Q, rfl⟩ := hUnit
  have h := S.mul_mem hAS (interior_subset hfA)
  change (↑Q : RealMatrix n) * ((↑Q : RealMatrix n)⁻¹ * ↑V) ∈ S at h
  rwa [← Matrix.coe_units_inv, ← mul_assoc, Units.mul_inv, one_mul] at h

end ContinuousBilinear
