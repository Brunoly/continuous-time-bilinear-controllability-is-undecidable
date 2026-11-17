import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Algebra.Group.Submonoid.Basic

/-! Exact finite-piece controllability with real, unrestricted controls.
The generated submonoid below is algebraic, not a topological closure.
-/
namespace ContinuousBilinear

abbrev State (n : ℕ) := Fin n → ℝ
abbrev RealMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

structure Plant (R : Type*) where
  dimension : ℕ
  controls : ℕ
  drift : Matrix (Fin dimension) (Fin dimension) R
  control : Fin controls → Matrix (Fin dimension) (Fin dimension) R

abbrev IntegerPlant := Plant ℤ
abbrev RationalPlant := Plant ℚ

noncomputable def toReal {R : Type*} [CommRing R] [Algebra R ℝ]
    (P : Plant R) : Plant ℝ where
  dimension := P.dimension
  controls := P.controls
  drift := P.drift.map (algebraMap R ℝ)
  control i := (P.control i).map (algebraMap R ℝ)

noncomputable def generator (P : Plant ℝ) (u : Fin P.controls → ℝ) :
    RealMatrix P.dimension := P.drift + ∑ i, u i • P.control i

noncomputable def segmentTransition (P : Plant ℝ) (t : ℝ)
    (u : Fin P.controls → ℝ) : RealMatrix P.dimension :=
  NormedSpace.exp (t • generator P u)

noncomputable def transitionMonoid (P : Plant ℝ) :
    Submonoid (RealMatrix P.dimension) :=
  Submonoid.closure {M | ∃ (t : ℝ) (u : Fin P.controls → ℝ),
    0 ≤ t ∧ M = segmentTransition P t u}

/-- Time zero is admitted. -/
def GloballyControllable (P : Plant ℝ) : Prop :=
  ∀ x y : State P.dimension, x ≠ 0 → y ≠ 0 →
    ∃ M ∈ transitionMonoid P, Matrix.mulVec M x = y

/-- Integer instances used for the strongest stated reduction.
The dimension bound excludes vacuous or disconnected punctured spaces.
It is a promised output of the compiler, not an assumption on all plants.
-/
def HasCanonicalDriftAndCommutingControls (P : IntegerPlant) : Prop :=
  2 ≤ P.dimension ∧
  P.drift = Matrix.diagonal (fun i => if i.val = 0 then 1 else 0) ∧
  ∀ i j, Commute (P.control i) (P.control j)

end ContinuousBilinear
