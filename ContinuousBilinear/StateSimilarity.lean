import ContinuousBilinear.TransitionProducts

namespace ContinuousBilinear

private def conjugation {n : ℕ} (U : (RealMatrix n)ˣ) : RealMatrix n →* RealMatrix n where
  toFun A := (U : RealMatrix n) * A * ↑U⁻¹
  map_one' := by simp
  map_mul' A B := by simp [mul_assoc]

/-- The plant in coordinates obtained by applying the invertible matrix U to each state. -/
abbrev conjugatePlant (P : Plant ℝ) (U : (RealMatrix P.dimension)ˣ) : Plant ℝ :=
  { P with drift := conjugation U P.drift
           control := fun i => conjugation U (P.control i) }

private theorem conjugation_smul {n : ℕ} (U : (RealMatrix n)ˣ) (t : ℝ) (A : RealMatrix n) :
    conjugation U (t • A) = t • conjugation U A := by
  change (U : RealMatrix n) * (t • A) * ↑U⁻¹ = _
  rw [Matrix.mul_smul, Matrix.smul_mul]
  rfl

private theorem generator_conjugate (P : Plant ℝ) (U : (RealMatrix P.dimension)ˣ)
    (u : Fin P.controls → ℝ) :
    generator (conjugatePlant P U) u = conjugation U (generator P u) := by
  simp only [generator, conjugatePlant]
  change _ = (U : RealMatrix P.dimension) * (_ + ∑ i, _) * ↑U⁻¹
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sum, Matrix.sum_mul,
    conjugation, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.mul_smul, Matrix.smul_mul]

theorem generator_conjugate_mulVec (P : Plant ℝ) (U : (RealMatrix P.dimension)ˣ)
    (u : Fin P.controls → ℝ) (z : State P.dimension) :
    (generator (conjugatePlant P U) u).mulVec ((↑U : RealMatrix P.dimension).mulVec z) =
      (↑U : RealMatrix P.dimension).mulVec ((generator P u).mulVec z) := by
  rw [generator_conjugate, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  change ((↑U : RealMatrix P.dimension) * generator P u * ↑U⁻¹ * ↑U).mulVec z =
    ((↑U : RealMatrix P.dimension) * generator P u).mulVec z
  rw [mul_assoc (_ * _) _ _, Units.inv_mul, mul_one]

theorem transitionMonoid_conjugate (P : Plant ℝ) (U : (RealMatrix P.dimension)ˣ) :
    transitionMonoid (conjugatePlant P U) = (transitionMonoid P).map (conjugation U) := by
  rw [transitionMonoid, transitionMonoid, MonoidHom.map_mclosure]
  congr 1
  ext M
  change (∃ (t : ℝ) (u : Fin P.controls → ℝ), 0 ≤ t ∧
    M = segmentTransition (conjugatePlant P U) t u) ↔ _
  have hseg (t : ℝ) (u : Fin P.controls → ℝ) :
      segmentTransition (conjugatePlant P U) t u =
        conjugation U (segmentTransition P t u) := by
    unfold segmentTransition
    rw [generator_conjugate, ← conjugation_smul]
    exact Matrix.exp_units_conj U _
  constructor
  · rintro ⟨t, u, ht, rfl⟩
    exact ⟨segmentTransition P t u, ⟨t, u, ht, rfl⟩, (hseg t u).symm⟩
  · rintro ⟨A, ⟨t, u, ht, rfl⟩, rfl⟩
    exact ⟨t, u, ht, (hseg t u).symm⟩

private theorem globallyControllable_conjugate_of (P : Plant ℝ)
    (U : (RealMatrix P.dimension)ˣ) (h : GloballyControllable P) :
    GloballyControllable (conjugatePlant P U) := by
  intro x y hx hy
  let V : RealMatrix P.dimension := ↑U⁻¹
  have hinv (z : State P.dimension) : (↑U : RealMatrix P.dimension).mulVec (V.mulVec z) = z := by
    rw [Matrix.mulVec_mulVec]
    simp [V]
  have nonzero (z : State P.dimension) (hz : z ≠ 0) : V.mulVec z ≠ 0 := by
    intro hzero
    exact hz (by simpa [hzero] using (hinv z).symm)
  obtain ⟨A, hA, hxy⟩ := h _ _ (nonzero x hx) (nonzero y hy)
  refine ⟨conjugation U A, ?_, ?_⟩
  · rw [transitionMonoid_conjugate]
    exact ⟨A, hA, rfl⟩
  · change ((↑U : RealMatrix P.dimension) * A * V).mulVec x = y
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hxy, hinv]

theorem conjugatePlant_inv (P : Plant ℝ) (U : (RealMatrix P.dimension)ˣ) :
    conjugatePlant (conjugatePlant P U) U⁻¹ = P := by
  have cancel (A : RealMatrix P.dimension) : conjugation U⁻¹ (conjugation U A) = A := by
    change (↑U⁻¹ : RealMatrix P.dimension) * (↑U * A * ↑U⁻¹) * ↑(U⁻¹)⁻¹ = A
    rw [inv_inv]
    calc
      _ = ((↑U⁻¹ : RealMatrix P.dimension) * ↑U) * A * (↑U⁻¹ * ↑U) := by
        simp only [mul_assoc]
      _ = A := by simp
  cases P
  simp only [conjugatePlant, cancel]

theorem globallyControllable_conjugate (P : Plant ℝ) (U : (RealMatrix P.dimension)ˣ) :
    GloballyControllable (conjugatePlant P U) ↔ GloballyControllable P := by
  refine ⟨fun h => ?_, globallyControllable_conjugate_of P U⟩
  exact conjugatePlant_inv P U ▸ globallyControllable_conjugate_of (conjugatePlant P U) U⁻¹ h

end ContinuousBilinear
