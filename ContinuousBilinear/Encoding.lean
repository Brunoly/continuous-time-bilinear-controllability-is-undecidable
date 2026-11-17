import ContinuousBilinear.Definitions
import Mathlib.Computability.Reduce
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Rat.Denumerable
import Mathlib.Algebra.MvPolynomial.Basic

namespace ContinuousBilinear

/-- Dimension, row-major drift entries, and a list of row-major control matrices. -/
abbrev PlantCode (R : Type*) := ℕ × List R × List (List R)
abbrev IntegerPlantCode := PlantCode ℤ
abbrev RationalPlantCode := PlantCode ℚ

namespace PlantCode

def WellFormed {R : Type*} (c : PlantCode R) : Prop :=
  c.2.1.length = c.1 * c.1 ∧ ∀ b ∈ c.2.2, b.length = c.1 * c.1

/-- Total decoding. Decision predicates reject malformed lists explicitly. -/
def decode {R : Type*} [Zero R] (c : PlantCode R) : Plant R where
  dimension := c.1
  controls := c.2.2.length
  drift i j := c.2.1.getD (i.val * c.1 + j.val) 0
  control k i j := (c.2.2.get k).getD (i.val * c.1 + j.val) 0

def map {R S : Type*} (f : R → S) (c : PlantCode R) : PlantCode S :=
  (c.1, c.2.1.map f, c.2.2.map (List.map f))

end PlantCode

noncomputable def IntegerGlobalControllability (c : IntegerPlantCode) : Prop :=
  c.WellFormed ∧ GloballyControllable (toReal c.decode)

noncomputable def RationalGlobalControllability (c : RationalPlantCode) : Prop :=
  c.WellFormed ∧ GloballyControllable (toReal c.decode)

def CanonicalIntegerInstance (c : IntegerPlantCode) : Prop :=
  c.WellFormed ∧ HasCanonicalDriftAndCommutingControls c.decode

/-- Sparse integer polynomial syntax: coefficient and finite exponent list.
The maximum exponent-list length fixes the finite variable set.
-/
abbrev IntegerPolynomialCode := List (ℤ × List ℕ)

namespace IntegerPolynomialCode

def arity (p : IntegerPolynomialCode) : ℕ :=
  (p.map fun t => t.2.length).foldr max 0

noncomputable def denote (p : IntegerPolynomialCode) : MvPolynomial (Fin p.arity) ℤ :=
  (p.map fun t => MvPolynomial.C t.1 *
    ∏ i : Fin p.arity, MvPolynomial.X i ^ t.2.getD i.val 0).sum

def HasIntegerRoot (p : IntegerPolynomialCode) : Prop :=
  ∃ x : Fin p.arity → ℤ, MvPolynomial.eval x p.denote = 0

end IntegerPolynomialCode

end ContinuousBilinear
