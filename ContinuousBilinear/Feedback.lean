import ContinuousBilinear.Definitions
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Span.Defs

namespace ContinuousBilinear

/-- Dimension d and number m of commuting generators are independent. -/
structure FeedbackData (d m : ℕ) where
  K : Fin m → RealMatrix d
  b : State d
  ell : State d

namespace FeedbackData

noncomputable def orbitMatrix {d m : ℕ} (F : FeedbackData d m) (t : Fin m → ℝ) :
    RealMatrix d := NormedSpace.exp (∑ i, t i • F.K i)

def pairing {d m : ℕ} (F : FeedbackData d m) (z : State d) : ℝ :=
  ∑ i, F.ell i * z i

def Hypotheses {d m : ℕ} (F : FeedbackData d m) : Prop :=
  (∀ i j, Commute (F.K i) (F.K j)) ∧
  F.pairing F.b = 1 ∧
  Submodule.span ℝ (Set.range fun t => Matrix.mulVec (F.orbitMatrix t) F.b) = ⊤ ∧
  Submodule.span ℝ (Set.range fun t => fun j =>
    ∑ i, F.ell i * F.orbitMatrix t i j) = ⊤

def HasNegativePairing {d m : ℕ} (F : FeedbackData d m) : Prop :=
  ∃ t : Fin m → ℝ, F.pairing (Matrix.mulVec (F.orbitMatrix t) F.b) < 0

/-- Coordinates are (s,z), with the added scalar at index zero.
This reverses the block order (z,s) used in equation (4.2) of the manuscript.
-/
noncomputable def plant {d m : ℕ} (F : FeedbackData d m) : Plant ℝ where
  dimension := d + 1
  controls := m + 1
  drift i j := (1 / 2 : ℝ) * Fin.cases 1 F.b i * Fin.cases 1 F.ell j
  control := Fin.cases
    (Matrix.diagonal (Fin.cases 0 (fun _ : Fin d => (1 : ℝ))))
    (fun k => fun i j => Fin.cases 0 (fun a => Fin.cases 0 (fun b => F.K k a b) j) i)

end FeedbackData
end ContinuousBilinear
