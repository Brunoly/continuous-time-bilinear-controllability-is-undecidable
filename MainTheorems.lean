import scripts.MatrixStatementProofs
import ContinuousBilinear.IntegrableControlCaratheodory

/-! Matrix formulations of Theorems A and A+, with control definitions and
analytic equivalences. -/

namespace BilinearControllability

/-- A finite input to an algorithm: dimension, drift entries, control matrices. -/
abbrev MatrixInput (K : Type) := ℕ × List K × List (List K)

/-- List the entries of each matrix, by rows, in the same order for every plant. -/
def matrixInput {K : Type} {n m : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (B : Fin m → Matrix (Fin n) (Fin n) K) : MatrixInput K :=
  let entries (M : Matrix (Fin n) (Fin n) K) :=
    List.ofFn fun i : Fin (n * n) => M (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  (n, entries A, List.ofFn fun i => entries (B i))

/-- The matrix of the vector field `x ↦ (A + ∑ i, u i • B i).mulVec x`. -/
noncomputable def generator {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Fin m → Matrix (Fin n) (Fin n) ℝ) (u : Fin m → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  A + ∑ i, u i • B i

/-- Chronological constant-control intervals. Later intervals multiply on the
left; the empty list gives the identity transition. -/
noncomputable def finiteTransition {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (steps : List (ℝ × (Fin m → ℝ))) : Matrix (Fin n) (Fin n) ℝ :=
  steps.foldl (fun M s => NormedSpace.exp (s.1 • generator A B s.2) * M) 1

/-- Exact reachability by finitely many constant-control intervals of positive
length. The empty list permits the zero-time trajectory. -/
noncomputable def PiecewiseConstantReachable {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (x y : Fin n → ℝ) : Prop :=
  ∃ steps : List (ℝ × (Fin m → ℝ)),
    (∀ s ∈ steps, 0 < s.1) ∧ (finiteTransition A B steps).mulVec x = y

/-- Exact control between every pair of nonzero real states, with
piecewise-constant real controls and a finite nonnegative time horizon. -/
noncomputable def GloballyControllable {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Fin m → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ x y : Fin n → ℝ, x ≠ 0 → y ≠ 0 → PiecewiseConstantReachable A B x y

/-- Exact reachability with integrable real controls on the finite horizon,
using the integral equation for the bilinear system. -/
noncomputable def IntegrableControlReachable {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (x y : Fin n → ℝ) : Prop :=
  ∃ (T : ℝ) (u : ℝ → Fin m → ℝ) (z : ℝ → Fin n → ℝ),
    0 ≤ T ∧ MeasureTheory.IntegrableOn u (Set.Icc 0 T) ∧
    ContinuousOn z (Set.Icc 0 T) ∧ z 0 = x ∧ z T = y ∧
    ∀ t ∈ Set.Icc 0 T,
      z t = x + ∫ s in (0 : ℝ)..t, (generator A B (u s)).mulVec (z s)

/-- Global controllability for finite-horizon integrable real controls. -/
noncomputable def GloballyControllableWithIntegrableControls {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Fin m → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ x y : Fin n → ℝ, x ≠ 0 → y ≠ 0 → IntegrableControlReachable A B x y

private theorem controllable_iff {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (B : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    GloballyControllable A B ↔
      ContinuousBilinear.GloballyControllable ⟨n, m, A, B⟩ := by
  let P : ContinuousBilinear.Plant ℝ := ⟨n, m, A, B⟩
  constructor
  · intro h x y hx hy
    obtain ⟨steps, hpos, hxy⟩ := h x y hx hy
    refine ⟨ContinuousBilinear.finiteTransition P steps, ?_, hxy⟩
    exact (ContinuousBilinear.transitionProductSemantics P _).mpr ⟨steps, hpos, rfl⟩
  · intro h x y hx hy
    obtain ⟨M, hM, hxy⟩ := h x y hx hy
    obtain ⟨steps, hpos, rfl⟩ := (ContinuousBilinear.transitionProductSemantics P M).mp hM
    exact ⟨steps, hpos, hxy⟩

/-- Piecewise-constant controls are admissible integrable controls. -/
theorem GloballyControllable.integrableControls {n m : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ} {B : Fin m → Matrix (Fin n) (Fin n) ℝ}
    (h : GloballyControllable A B) : GloballyControllableWithIntegrableControls A B :=
  ((controllable_iff A B).mp h).integrableControls

/-- Extending a finite-horizon control by zero gives the equivalent
formulation with locally integrable controls on the nonnegative time axis. -/
theorem integrableControlReachable_iff_locallyIntegrableOn {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (x y : Fin n → ℝ) :
    IntegrableControlReachable A B x y ↔
      ∃ (T : ℝ) (u : ℝ → Fin m → ℝ) (z : ℝ → Fin n → ℝ),
        0 ≤ T ∧ MeasureTheory.LocallyIntegrableOn u (Set.Ici 0) ∧
        ContinuousOn z (Set.Icc 0 T) ∧ z 0 = x ∧ z T = y ∧
        ∀ t ∈ Set.Icc 0 T,
          z t = x + ∫ s in (0 : ℝ)..t, (generator A B (u s)).mulVec (z s) :=
  ContinuousBilinear.integrableControlReachable_iff_locallyIntegrableOn ⟨n, m, A, B⟩ x y

/-- The integral equation agrees with the absolutely continuous,
almost-everywhere differential-equation formulation of Carathéodory. -/
theorem integralEquation_iff_caratheodory {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Fin m → Matrix (Fin n) (Fin n) ℝ)
    {T : ℝ} (hT : 0 ≤ T) {u : ℝ → Fin m → ℝ}
    (hu : MeasureTheory.IntegrableOn u (Set.Icc 0 T)) {z : ℝ → Fin n → ℝ} :
    (ContinuousOn z (Set.Icc 0 T) ∧ ∀ t ∈ Set.Icc 0 T,
      z t = z 0 + ∫ s in (0 : ℝ)..t, (generator A B (u s)).mulVec (z s)) ↔
    (AbsolutelyContinuousOnInterval z 0 T ∧
      ∀ᵐ t, t ∈ Set.Icc 0 T → HasDerivAt z ((generator A B (u t)).mulVec (z t)) t) :=
  ContinuousBilinear.integralEquation_iff_absolutelyContinuous_and_ae_hasDerivAt
    ⟨n, m, A, B⟩ hT hu

/-- Theorem A. Global controllability is undecidable for rational matrices. -/
theorem rationalUndecidability :
    ¬ ∃ decide : MatrixInput ℚ → Bool, Computable decide ∧
      ∀ {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) (B : Fin m → Matrix (Fin n) (Fin n) ℚ),
        decide (matrixInput A B) = true ↔
          GloballyControllable (A.map (algebraMap ℚ ℝ)) (fun i => (B i).map (algebraMap ℚ ℝ)) := by
  rintro ⟨decide, hcomp, h⟩
  exact ContinuousBilinear.rationalMatrixUndecidability
    ⟨decide, hcomp, fun P => (h P.drift P.control).trans (controllable_iff _ _)⟩

/-- Theorem A+. A partial recursive algorithm cannot decide controllability
even when it need only halt and answer correctly on canonical integer inputs. -/
theorem canonicalIntegerUndecidability :
    ¬ ∃ decide : MatrixInput ℤ →. Bool, Partrec decide ∧
      ∀ {n m : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (B : Fin m → Matrix (Fin n) (Fin n) ℤ),
        2 ≤ n → A = Matrix.diagonal (fun i => if i.val = 0 then 1 else 0) →
        (∀ i j, Commute (B i) (B j)) →
        ∃ b : Bool, b ∈ decide (matrixInput A B) ∧
          (b = true ↔ GloballyControllable (A.map (algebraMap ℤ ℝ))
            (fun i => (B i).map (algebraMap ℤ ℝ))) := by
  rintro ⟨decide, hcomp, h⟩
  apply ContinuousBilinear.canonicalIntegerMatrixUndecidability
  refine ⟨decide, hcomp, fun P hP => ?_⟩
  obtain ⟨b, hb, hEq⟩ := h P.drift P.control hP.1 hP.2.1 hP.2.2
  exact ⟨b, hb, hEq.trans (controllable_iff _ _)⟩

end BilinearControllability

#print axioms BilinearControllability.rationalUndecidability
#print axioms BilinearControllability.canonicalIntegerUndecidability

#print axioms BilinearControllability.GloballyControllable.integrableControls
#print axioms BilinearControllability.integrableControlReachable_iff_locallyIntegrableOn
#print axioms BilinearControllability.integralEquation_iff_caratheodory
