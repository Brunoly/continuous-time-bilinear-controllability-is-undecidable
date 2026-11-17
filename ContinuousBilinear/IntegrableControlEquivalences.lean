import ContinuousBilinear.IntegrableControlTransport
import ContinuousBilinear.StateSimilarity

namespace ContinuousBilinear

private noncomputable def stateCoordinates {n : ℕ} (U : (RealMatrix n)ˣ) :
    State n ≃L[ℝ] State n :=
  LinearEquiv.toContinuousLinearEquiv
    { toLinearMap := Matrix.mulVecLin (↑U : RealMatrix n)
      invFun := fun x => (↑U⁻¹ : RealMatrix n).mulVec x
      left_inv := fun x => by
        change (↑U⁻¹ : RealMatrix n).mulVec ((↑U : RealMatrix n).mulVec x) = x
        rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      right_inv := fun x => by
        change (↑U : RealMatrix n).mulVec ((↑U⁻¹ : RealMatrix n).mulVec x) = x
        rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] }

theorem globallyControllableWithIntegrableControls_conjugate_of
    (P : Plant ℝ) (U : (RealMatrix P.dimension)ˣ)
    (h : GloballyControllableWithIntegrableControls P) :
    GloballyControllableWithIntegrableControls (conjugatePlant P U) := by
  let E := stateCoordinates U
  intro x y hx hy
  have hnonzero (z : State P.dimension) (hz : z ≠ 0) : E.symm z ≠ 0 := by
    intro hzero
    apply hz
    simpa using congrArg E hzero
  have hxy := h (E.symm x) (E.symm y) (hnonzero x hx) (hnonzero y hy)
  have hp := integrableControlReachable_map P (conjugatePlant P U) E
    (ContinuousLinearMap.id ℝ (Fin P.controls → ℝ))
    (fun u z => (generator_conjugate_mulVec P U u z).symm) hxy
  simpa only [ContinuousLinearEquiv.apply_symm_apply] using hp

theorem globallyControllableWithIntegrableControls_conjugate
    (P : Plant ℝ) (U : (RealMatrix P.dimension)ˣ) :
    GloballyControllableWithIntegrableControls (conjugatePlant P U) ↔
      GloballyControllableWithIntegrableControls P := by
  refine ⟨fun h => ?_, globallyControllableWithIntegrableControls_conjugate_of P U⟩
  exact conjugatePlant_inv P U ▸
    globallyControllableWithIntegrableControls_conjugate_of (conjugatePlant P U) U⁻¹ h

private noncomputable def controlScale {m : ℕ} (scale : Fin m → ℝ) :
    (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v i => v i * scale i
      map_add' := fun _ _ => funext fun _ => add_mul _ _ _
      map_smul' := fun _ _ => funext fun _ => mul_assoc _ _ _ }

theorem globallyControllableWithIntegrableControls_of_rescale_controls
    (P : Plant ℝ) (scale : Fin P.controls → ℝ)
    (h : GloballyControllableWithIntegrableControls
      {P with control := fun i => scale i • P.control i}) :
    GloballyControllableWithIntegrableControls P := by
  let Q : Plant ℝ := {P with control := fun i => scale i • P.control i}
  intro x y hx hy
  have hField (v : Fin P.controls → ℝ) (z : State P.dimension) :
      (generator Q v).mulVec z = (generator P (controlScale scale v)).mulVec z := by
    simp [generator, Q, smul_smul, controlScale]
  exact integrableControlReachable_map Q P (ContinuousLinearEquiv.refl ℝ (State P.dimension))
    (controlScale scale) hField (h x y hx hy)

theorem globallyControllableWithIntegrableControls_rescale_controls
    (P : Plant ℝ) (scale : Fin P.controls → ℝ) (hscale : ∀ i, scale i ≠ 0) :
    GloballyControllableWithIntegrableControls {P with control := fun i => scale i • P.control i} ↔
      GloballyControllableWithIntegrableControls P := by
  refine ⟨globallyControllableWithIntegrableControls_of_rescale_controls P scale, ?_⟩
  intro h
  let Q : Plant ℝ := {P with control := fun i => scale i • P.control i}
  have heq : {Q with control := fun i => (scale i)⁻¹ • Q.control i} = P := by
    cases P
    simp [Q, smul_smul, hscale]
  exact globallyControllableWithIntegrableControls_of_rescale_controls Q
    (fun i => (scale i)⁻¹) (heq.symm ▸ h)

end ContinuousBilinear
