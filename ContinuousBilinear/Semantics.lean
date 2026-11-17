import ContinuousBilinear.Definitions
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

namespace ContinuousBilinear

abbrev Segment (m : ℕ) := ℝ × (Fin m → ℝ)

def PositiveDurations {m : ℕ} (steps : List (Segment m)) : Prop :=
  ∀ s ∈ steps, 0 < s.1

/-- The last chronological interval multiplies on the left. -/
noncomputable def finiteTransition (P : Plant ℝ) (steps : List (Segment P.controls)) :
    RealMatrix P.dimension :=
  steps.foldl (fun M s => segmentTransition P s.1 s.2 * M) 1

/-- A classical solution of one constant-control interval of positive length. -/
def ConstantControlSegment (P : Plant ℝ) (x y : State P.dimension) : Prop :=
  ∃ (T : ℝ) (u : Fin P.controls → ℝ) (z : ℝ → State P.dimension),
    0 < T ∧ z 0 = x ∧ z T = y ∧
    ∀ t ∈ Set.Icc 0 T,
      HasDerivWithinAt z (Matrix.mulVec (generator P u) (z t)) (Set.Icc 0 T) t

/-- Finite concatenation; reflexivity is the allowed zero-time trajectory. -/
def PiecewiseConstantReachable (P : Plant ℝ) : State P.dimension → State P.dimension → Prop :=
  Relation.ReflTransGen (ConstantControlSegment P)

/-- Integral-equation formulation on a finite horizon, with real L1 controls.
Together with continuity, this expresses the usual absolutely continuous solution.
-/
def IntegrableControlReachable (P : Plant ℝ) (x y : State P.dimension) : Prop :=
  ∃ (T : ℝ) (u : ℝ → Fin P.controls → ℝ) (z : ℝ → State P.dimension),
    0 ≤ T ∧ MeasureTheory.IntegrableOn u (Set.Icc 0 T) ∧
    ContinuousOn z (Set.Icc 0 T) ∧ z 0 = x ∧ z T = y ∧
    ∀ t ∈ Set.Icc 0 T,
      z t = x + ∫ s in (0 : ℝ)..t, Matrix.mulVec (generator P (u s)) (z s)

def GloballyControllableWithIntegrableControls (P : Plant ℝ) : Prop :=
  ∀ x y : State P.dimension, x ≠ 0 → y ≠ 0 → IntegrableControlReachable P x y

end ContinuousBilinear
