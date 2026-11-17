import ContinuousBilinear.CompilerDenominatorClearingProof
import ContinuousBilinear.ControlRescaling

namespace ContinuousBilinear

namespace Plant

open PlantCode

/-- For a rational plant whose drift is already canonical, the integer
presentation uses the same drift and clears each control matrix separately. -/
def clearControlDenominators (P : Plant ℚ) : IntegerPlant where
  dimension := P.dimension
  controls := P.controls
  drift := Matrix.diagonal fun i => if i.val = 0 then 1 else 0
  control k i j := (clearDenominators (matrixEntries (P.control k))).getD
    (i.val * P.dimension + j.val) 0

theorem clearControlDenominators_control_map (P : Plant ℚ) (k : Fin P.controls) :
    (P.clearControlDenominators.control k).map (Int.castRingHom ℚ) =
      (commonDenominator (matrixEntries (P.control k)) : ℚ) • P.control k := by
  apply Matrix.ext
  intro i j
  change (((clearDenominators (matrixEntries (P.control k))).getD
    (i.val * P.dimension + j.val) 0 : ℤ) : ℚ) =
      (commonDenominator (matrixEntries (P.control k)) : ℚ) * P.control k i j
  exact (cast_clearDenominators_getD _ _).trans
    (congrArg (fun q : ℚ => (commonDenominator (matrixEntries (P.control k)) : ℚ) * q)
      (matrixEntries_getD (P.control k) i j 0))

theorem canonical_clearControlDenominators (P : Plant ℚ) (hdim : 2 ≤ P.dimension)
    (hcomm : ∀ i j, Commute (P.control i) (P.control j)) :
    HasCanonicalDriftAndCommutingControls P.clearControlDenominators := by
  refine ⟨hdim, rfl, fun i j => ?_⟩
  change P.clearControlDenominators.control i * P.clearControlDenominators.control j =
    P.clearControlDenominators.control j * P.clearControlDenominators.control i
  have hinj : Function.Injective (fun M : Matrix (Fin P.dimension) (Fin P.dimension) ℤ =>
      M.map (Int.castRingHom ℚ)) := Matrix.map_injective Int.cast_injective
  apply hinj
  change (P.clearControlDenominators.control i * P.clearControlDenominators.control j).map
    (Int.castRingHom ℚ) =
      (P.clearControlDenominators.control j * P.clearControlDenominators.control i).map
        (Int.castRingHom ℚ)
  have hmul (k l : Fin P.controls) :
      (P.clearControlDenominators.control k * P.clearControlDenominators.control l).map
        (Int.castRingHom ℚ) =
      ((commonDenominator (matrixEntries (P.control k)) : ℚ) • P.control k) *
        ((commonDenominator (matrixEntries (P.control l)) : ℚ) • P.control l) :=
    (Matrix.map_mul (f := Int.castRingHom ℚ)).trans
      (congrArg₂ (· * ·) (clearControlDenominators_control_map P k)
        (clearControlDenominators_control_map P l))
  rw [hmul i j, hmul j i]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  rw [(hcomm i j).eq]
  congr 1
  exact mul_comm _ _

noncomputable def controlDenominatorScale (P : Plant ℚ) (k : Fin P.controls) : ℝ :=
  commonDenominator (matrixEntries (P.control k))

theorem controlDenominatorScale_ne_zero (P : Plant ℚ) (k : Fin P.controls) :
    P.controlDenominatorScale k ≠ 0 := by
  change (commonDenominator (matrixEntries (P.control k)) : ℝ) ≠ 0
  exact_mod_cast (commonDenominator_pos (matrixEntries (P.control k))).ne'

theorem toReal_clearControlDenominators (P : Plant ℚ)
    (hdrift : P.drift = Matrix.diagonal (fun i => if i.val = 0 then 1 else 0)) :
    toReal P.clearControlDenominators =
      { toReal P with control := fun k => P.controlDenominatorScale k • (toReal P).control k } := by
  let c := toReal P
  let scale := P.controlDenominatorScale
  have hA : (toReal P.clearControlDenominators).drift = c.drift := by
    change (Matrix.diagonal (fun i : Fin P.dimension => if i.val = 0 then (1 : ℤ) else 0)).map
      (algebraMap ℤ ℝ) = P.drift.map (algebraMap ℚ ℝ)
    rw [hdrift, Matrix.diagonal_map (map_zero (algebraMap ℤ ℝ)),
      Matrix.diagonal_map (map_zero (algebraMap ℚ ℝ))]
    congr 1
    funext i
    by_cases hi : i.val = 0 <;> simp [hi]
  have hB (k : Fin P.controls) :
      (toReal P.clearControlDenominators).control k = scale k • c.control k := by
    apply Matrix.ext
    intro i j
    have hq := congrArg (fun M : Matrix (Fin P.dimension) (Fin P.dimension) ℚ => M i j)
      (clearControlDenominators_control_map P k)
    change ((P.clearControlDenominators.control k i j : ℤ) : ℚ) =
      (commonDenominator (matrixEntries (P.control k)) : ℚ) * P.control k i j at hq
    change ((P.clearControlDenominators.control k i j : ℤ) : ℝ) =
      (commonDenominator (matrixEntries (P.control k)) : ℝ) * (P.control k i j : ℝ)
    exact_mod_cast hq
  change Plant.mk P.dimension P.controls (toReal P.clearControlDenominators).drift
    (toReal P.clearControlDenominators).control =
    Plant.mk P.dimension P.controls c.drift (fun k => scale k • c.control k)
  exact congrArg₂ (Plant.mk P.dimension P.controls) hA (funext hB)

theorem globallyControllable_clearControlDenominators (P : Plant ℚ)
    (hdrift : P.drift = Matrix.diagonal (fun i => if i.val = 0 then 1 else 0)) :
    GloballyControllable (toReal P.clearControlDenominators) ↔
      GloballyControllable (toReal P) := by
  rw [toReal_clearControlDenominators P hdrift]
  exact globallyControllable_rescale_controls (toReal P) P.controlDenominatorScale
    P.controlDenominatorScale_ne_zero

end Plant

theorem exists_integerPlantCode_of_canonicalRationalPlant (P : Plant ℚ)
    (hdim : 2 ≤ P.dimension)
    (hdrift : P.drift = Matrix.diagonal (fun i => if i.val = 0 then 1 else 0))
    (hcomm : ∀ i j, Commute (P.control i) (P.control j)) :
    ∃ c : IntegerPlantCode, CanonicalIntegerInstance c ∧
      (IntegerGlobalControllability c ↔ GloballyControllable (toReal P)) := by
  let I := P.clearControlDenominators
  refine ⟨PlantCode.encode I, ?_, ?_⟩
  · exact ⟨PlantCode.wellFormed_encode I,
      by rw [PlantCode.decode_encode]; exact P.canonical_clearControlDenominators hdim hcomm⟩
  · unfold IntegerGlobalControllability
    rw [PlantCode.decode_encode, and_iff_right (PlantCode.wellFormed_encode I)]
    exact P.globallyControllable_clearControlDenominators hdrift

end ContinuousBilinear
