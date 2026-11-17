import ContinuousBilinear.Encoding
import ContinuousBilinear.Semantics
import ContinuousBilinear.Feedback
import ContinuousBilinear.SignEncoding

/-! Propositions specifying the reduction, its semantics, and undecidability.
-/
namespace ContinuousBilinear.Targets

open IntegerPolynomialCode

/-- The reduction produces a canonical integer instance for every polynomial input. -/
def IntegerReduction : Prop :=
  ∃ f : IntegerPolynomialCode → IntegerPlantCode,
    Computable f ∧ ∀ p,
      CanonicalIntegerInstance (f p) ∧
      (HasIntegerRoot p ↔ IntegerGlobalControllability (f p))

def IntegerUndecidability : Prop := ¬ ComputablePred IntegerGlobalControllability

def RationalUndecidability : Prop := ¬ ComputablePred RationalGlobalControllability

/-- Total-decider formulation of the restricted problem. -/
def CanonicalIntegerNoTotalDecider : Prop :=
  ¬ ∃ decide : IntegerPlantCode → Bool, Computable decide ∧
    ∀ c, CanonicalIntegerInstance c →
      (decide c = true ↔ GloballyControllable (toReal c.decode))

/-- The algorithm is required to halt and answer correctly on canonical inputs.
Outside the promise it may return either answer or diverge.
-/
def CanonicalIntegerUndecidability : Prop :=
  ¬ ∃ decide : IntegerPlantCode →. Bool, Partrec decide ∧
    ∀ c, CanonicalIntegerInstance c →
      ∃ b : Bool, b ∈ decide c ∧
        (b = true ↔ GloballyControllable (toReal c.decode))

/-- Finite syntactic validation must itself be computable. -/
def InputValidationComputable : Prop :=
  ComputablePred (PlantCode.WellFormed (R := ℤ)) ∧
  ComputablePred (PlantCode.WellFormed (R := ℚ)) ∧
  ComputablePred CanonicalIntegerInstance

def IntegerToRationalTransport : Prop :=
  Computable (PlantCode.map (fun z : ℤ => (z : ℚ))) ∧
  ∀ c : IntegerPlantCode, IntegerGlobalControllability c ↔
    RationalGlobalControllability (c.map (fun z : ℤ => (z : ℚ)))

/-- Integer-polynomial undecidability in the finite polynomial representation. -/
def IntegerHilbertTenth : Prop := ¬ ComputablePred HasIntegerRoot

/-- Every matrix tuple has a valid finite presentation; decoding loses no instances. -/
def EncodingCompleteness : Prop :=
  (∀ P : IntegerPlant, ∃ c : IntegerPlantCode, c.WellFormed ∧ c.decode = P) ∧
  (∀ P : RationalPlant, ∃ c : RationalPlantCode, c.WellFormed ∧ c.decode = P)

def TransitionProductSemantics : Prop :=
  ∀ (P : Plant ℝ) (M : RealMatrix P.dimension),
    M ∈ transitionMonoid P ↔
    ∃ steps : List (Segment P.controls), PositiveDurations steps ∧
      finiteTransition P steps = M

def DifferentialEquationSemantics : Prop :=
  ∀ (P : Plant ℝ) (x y : State P.dimension),
    PiecewiseConstantReachable P x y ↔
      ∃ M ∈ transitionMonoid P, Matrix.mulVec M x = y

def FeedbackEquivalence : Prop :=
  ∀ (d m : ℕ) (F : FeedbackData d m), F.Hypotheses →
    (GloballyControllable F.plant ↔ F.HasNegativePairing)

/-- Equality of actual finite transitions, not equality of topological closures. -/
def FeedbackExactTransitions : Prop :=
  ∀ (d m : ℕ) (F : FeedbackData d m), F.Hypotheses → F.HasNegativePairing →
    ∀ M : RealMatrix (d + 1), M ∈ transitionMonoid F.plant ↔ 0 < Matrix.det M

/-- A common computable reduction for both control classes. -/
def IntegerReductionWithIntegrableControls : Prop :=
  ∃ f : IntegerPolynomialCode → IntegerPlantCode,
    Computable f ∧ ∀ p,
      CanonicalIntegerInstance (f p) ∧
      (HasIntegerRoot p ↔ IntegerGlobalControllability (f p)) ∧
      (HasIntegerRoot p ↔ GloballyControllableWithIntegrableControls (toReal (f p).decode))

def IntegrableIntegerUndecidability : Prop :=
  ¬ ComputablePred (fun c : IntegerPlantCode => c.WellFormed ∧
    GloballyControllableWithIntegrableControls (toReal c.decode))

def IntegrableRationalUndecidability : Prop :=
  ¬ ComputablePred (fun c : RationalPlantCode => c.WellFormed ∧
    GloballyControllableWithIntegrableControls (toReal c.decode))

end ContinuousBilinear.Targets
