import ContinuousBilinear.CompilerCanonicalDriftProof
import ContinuousBilinear.CompilerIntegerPlantProof
import ContinuousBilinear.StateSimilarity

namespace ContinuousBilinear

namespace FeedbackCoordinates

variable {d m : ℕ}

private abbrev RatMatrix (d : ℕ) := Matrix (Fin d) (Fin d) ℚ

/-- Extend a control matrix by zero in the scalar coordinate. -/
def controlBlock (M : RatMatrix d) : RatMatrix (d + 1) :=
  Matrix.of (Fin.cases 0 (fun i => Fin.cases 0 (M i)))

theorem controlBlock_mul (A B : RatMatrix d) :
    controlBlock (A * B) = controlBlock A * controlBlock B := by
  apply Matrix.ext
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [controlBlock, Matrix.mul_apply]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [controlBlock, Matrix.mul_apply, Fin.sum_univ_succ]
    · simp [controlBlock, Matrix.mul_apply, Fin.sum_univ_succ]

def rationalControls (K : Fin m → RatMatrix d) (k : Fin (m + 1)) :
    RatMatrix (d + 1) :=
  controlBlock (Fin.cases 1 K k)

def rationalFeedbackPlant (K : Fin m → RatMatrix d) (b ell : Fin d → ℚ) : Plant ℚ where
  dimension := d + 1
  controls := m + 1
  drift := rankOneDrift b ell
  control := rationalControls K

noncomputable def realFeedbackData (K : Fin m → RatMatrix d) (b ell : Fin d → ℚ) : FeedbackData d m where
  K i := (K i).map (algebraMap ℚ ℝ)
  b i := b i
  ell i := ell i

private theorem controlBlock_one (d : ℕ) :
    controlBlock (1 : RatMatrix d) = Matrix.diagonal (Fin.cases 0 (fun _ : Fin d => 1)) := by
  apply Matrix.ext
  intro i j
  refine Fin.cases ?_ (fun i => ?_) i
  · refine Fin.cases ?_ (fun j => ?_) j <;> simp [controlBlock, Matrix.diagonal_apply]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp [controlBlock]
    · simp [controlBlock, Matrix.diagonal_apply, Matrix.one_apply]

theorem toReal_rationalFeedbackPlant (K : Fin m → RatMatrix d) (b ell : Fin d → ℚ) :
    toReal (rationalFeedbackPlant K b ell) = (realFeedbackData K b ell).plant := by
  have hA : (rankOneDrift b ell).map (algebraMap ℚ ℝ) =
      (realFeedbackData K b ell).plant.drift := by
    apply Matrix.ext
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;>
      refine Fin.cases ?_ (fun j => ?_) j <;>
      simp [rankOneDrift, FeedbackData.plant, realFeedbackData]
  have hB (k : Fin (m + 1)) :
      (rationalControls K k).map (algebraMap ℚ ℝ) =
        (realFeedbackData K b ell).plant.control k := by
    refine Fin.cases ?_ (fun k => ?_) k
    · change (controlBlock (1 : RatMatrix d)).map (algebraMap ℚ ℝ) =
        Matrix.diagonal (Fin.cases (0 : ℝ) (fun _ : Fin d => 1))
      rw [controlBlock_one, Matrix.diagonal_map (map_zero (algebraMap ℚ ℝ))]
      congr 1
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    · change (controlBlock (K k)).map (algebraMap ℚ ℝ) =
        (fun i j => Fin.cases 0
          (fun a => Fin.cases 0 ((realFeedbackData K b ell).K k a) j) i :
            RealMatrix (d + 1))
      apply Matrix.ext
      intro i j
      refine Fin.cases ?_ (fun i => ?_) i <;>
        refine Fin.cases ?_ (fun j => ?_) j <;>
        simp [controlBlock, realFeedbackData]
  exact congrArg₂ (Plant.mk (d + 1) (m + 1)) hA (funext hB)

theorem rationalFeedback_commute (K : Fin m → RatMatrix d) (b ell : Fin d → ℚ)
    (hK : ∀ i j, Commute (K i) (K j)) (i j : Fin (m + 1)) :
    Commute ((rationalFeedbackPlant K b ell).control i)
      ((rationalFeedbackPlant K b ell).control j) := by
  change Commute (controlBlock (Fin.cases 1 K i)) (controlBlock (Fin.cases 1 K j))
  change controlBlock _ * controlBlock _ = controlBlock _ * controlBlock _
  rw [← controlBlock_mul, ← controlBlock_mul]
  congr 1
  refine Fin.cases ?_ (fun i => ?_) i
  · simp
  · refine Fin.cases ?_ (fun j => ?_) j
    · simp
    · exact (hK i j).eq

/-- Express the rational feedback plant in the explicit basis that diagonalizes
its rank-one drift. -/
def normalizedRationalFeedback (K : Fin m → RatMatrix d) (b ell : Fin d → ℚ) : Plant ℚ where
  dimension := d + 1
  controls := m + 1
  drift := canonicalDrift d
  control k := inverseMatrix b ell * rationalControls K k * basisMatrix b ell

theorem normalizedRationalFeedback_commute (K : Fin m → RatMatrix d)
    (b ell : Fin d → ℚ) (h : ∑ i, ell i * b i = 1)
    (hK : ∀ i j, Commute (K i) (K j)) (i j : Fin (m + 1)) :
    Commute ((normalizedRationalFeedback K b ell).control i)
      ((normalizedRationalFeedback K b ell).control j) := by
  let U := basisUnit b ell h
  let R : RatMatrix (d + 1) := ↑U
  let L : RatMatrix (d + 1) := ↑U⁻¹
  have hRL : R * L = 1 := Units.mul_inv U
  have hc (k : Fin (m + 1)) : (normalizedRationalFeedback K b ell).control k =
      L * rationalControls K k * R := rfl
  change _ * _ = _ * _
  rw [hc i, hc j]
  have hcomm : rationalControls K i * rationalControls K j =
      rationalControls K j * rationalControls K i :=
    (rationalFeedback_commute K b ell hK i j).eq
  have hmul (A B : RatMatrix (d + 1)) :
      (L * A * R) * (L * B * R) = L * (A * B) * R := by
    calc
      _ = L * A * (R * L) * B * R := by simp only [mul_assoc]
      _ = _ := by simp [hRL, mul_assoc]
  exact (hmul (rationalControls K i) (rationalControls K j)).trans
    ((congrArg (fun A : RatMatrix (d + 1) => L * A * R) hcomm).trans
      (hmul (rationalControls K j) (rationalControls K i)).symm)

private noncomputable def realMatrixCast (d : ℕ) : RatMatrix d →* RealMatrix d where
  toFun M := M.map (algebraMap ℚ ℝ)
  map_one' := by simp
  map_mul' A B := Matrix.map_mul (f := algebraMap ℚ ℝ)

noncomputable def normalizingSimilarity (b ell : Fin d → ℚ)
    (h : ∑ i, ell i * b i = 1) : (RealMatrix (d + 1))ˣ :=
  Units.map (realMatrixCast (d + 1)) (basisUnit b ell h)⁻¹

theorem toReal_normalizedRationalFeedback (K : Fin m → RatMatrix d)
    (b ell : Fin d → ℚ) (h : ∑ i, ell i * b i = 1) :
    toReal (normalizedRationalFeedback K b ell) =
      conjugatePlant (toReal (rationalFeedbackPlant K b ell)) (normalizingSimilarity b ell h) := by
  let P := toReal (rationalFeedbackPlant K b ell)
  let U := normalizingSimilarity b ell h
  have hA : (toReal (normalizedRationalFeedback K b ell)).drift =
      (conjugatePlant P U).drift := by
    change realMatrixCast (d + 1) (canonicalDrift d) =
      realMatrixCast (d + 1) (inverseMatrix b ell) *
        realMatrixCast (d + 1) (rankOneDrift b ell) *
          realMatrixCast (d + 1) (basisMatrix b ell)
    rw [← map_mul, ← map_mul, conjugate_drift b ell h]
  have hB (k : Fin (m + 1)) : (toReal (normalizedRationalFeedback K b ell)).control k =
      (conjugatePlant P U).control k := by
    change realMatrixCast (d + 1)
      (inverseMatrix b ell * rationalControls K k * basisMatrix b ell) =
      realMatrixCast (d + 1) (inverseMatrix b ell) *
        realMatrixCast (d + 1) (rationalControls K k) *
          realMatrixCast (d + 1) (basisMatrix b ell)
    rw [map_mul, map_mul]
  exact congrArg₂ (Plant.mk (d + 1) (m + 1)) hA (funext hB)

theorem globallyControllable_normalizedRationalFeedback (K : Fin m → RatMatrix d)
    (b ell : Fin d → ℚ) (h : ∑ i, ell i * b i = 1) :
    GloballyControllable (toReal (normalizedRationalFeedback K b ell)) ↔
      GloballyControllable (realFeedbackData K b ell).plant := by
  rw [toReal_normalizedRationalFeedback K b ell h]
  exact (globallyControllable_conjugate (toReal (rationalFeedbackPlant K b ell))
      (normalizingSimilarity b ell h)).trans
    (congrArg GloballyControllable (toReal_rationalFeedbackPlant K b ell) |> Iff.of_eq)

theorem exists_integerPlantCode_of_rationalFeedback (K : Fin m → RatMatrix d)
    (b ell : Fin d → ℚ) (h : ∑ i, ell i * b i = 1)
    (hK : ∀ i j, Commute (K i) (K j)) :
    ∃ c : IntegerPlantCode, CanonicalIntegerInstance c ∧
      (IntegerGlobalControllability c ↔ GloballyControllable (realFeedbackData K b ell).plant) := by
  have hd : 2 ≤ d + 1 := by
    by_contra hn
    obtain rfl : d = 0 := by omega
    simp at h
  obtain ⟨c, hc, hgc⟩ := exists_integerPlantCode_of_canonicalRationalPlant
    (normalizedRationalFeedback K b ell) hd rfl
    (normalizedRationalFeedback_commute K b ell h hK)
  exact ⟨c, hc, hgc.trans (globallyControllable_normalizedRationalFeedback K b ell h)⟩

end FeedbackCoordinates
end ContinuousBilinear
