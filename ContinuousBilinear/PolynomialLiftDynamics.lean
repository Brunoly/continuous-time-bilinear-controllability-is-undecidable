import ContinuousBilinear.PolynomialLiftOscillator
import ContinuousBilinear.ODEProof
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

namespace ContinuousBilinear
namespace PolynomialLift

open MvPolynomial
open scoped BigOperators Matrix

noncomputable section

def oscillatorTrajectory {n : ℕ} (u : OscillatorChannel n → ℝ)
    (t : ℝ) (x : OscillatorCoordinate n) : ℝ :=
  match x with
  | .inl _ => t * u none
  | .inr (j, k) =>
    if k = 0 then t * u (some j) else if k = 1 then Real.cos (t * u (some j))
    else Real.sin (t * u (some j))

def oscillatorBase (n : ℕ) (x : OscillatorCoordinate n) : ℤ :=
  match x with
  | .inl _ => 0
  | .inr (_, k) => if k = 1 then 1 else 0

theorem oscillatorTrajectory_zero {n : ℕ} (u : OscillatorChannel n → ℝ)
    (x : OscillatorCoordinate n) : oscillatorTrajectory u 0 x = oscillatorBase n x := by
  rcases x with _ | ⟨j, k⟩
  · simp [oscillatorTrajectory, oscillatorBase]
  · fin_cases k <;> simp [oscillatorTrajectory, oscillatorBase]

private theorem coordinate_derivative {n : ℕ} (u : OscillatorChannel n → ℝ)
    (t : ℝ) (x : OscillatorCoordinate n) :
    HasDerivAt (fun t => oscillatorTrajectory u t x)
      (∑ i, u i * (eval₂Hom (Int.castRingHom ℝ) (oscillatorTrajectory u t)) (oscillatorField i x))
      t := by
  rcases x with _ | ⟨j, k⟩
  · simpa [Fintype.sum_option, oscillatorField, oscillatorTrajectory] using
      (hasDerivAt_id t).mul_const (u none)
  · have h := (hasDerivAt_id t).mul_const (u (some j))
    have sum_field (s0 : Fin 3) :
        (∑ i, u i * (eval₂Hom (Int.castRingHom ℝ) (oscillatorTrajectory u t))
          (oscillatorField i (oscillatorCoordinate j s0))) =
          u (some j) * (eval₂Hom (Int.castRingHom ℝ) (oscillatorTrajectory u t))
            (oscillatorField (some j) (oscillatorCoordinate j s0)) := by
      rw [Fintype.sum_option, Finset.sum_eq_single j]
      · simp [oscillatorField, oscillatorCoordinate]
      · intro i _ hi
        simp [oscillatorField, oscillatorCoordinate, hi]
      · simp
    change HasDerivAt (fun t => oscillatorTrajectory u t (oscillatorCoordinate j k))
      (∑ i, u i * (eval₂Hom (Int.castRingHom ℝ) (oscillatorTrajectory u t))
        (oscillatorField i (oscillatorCoordinate j k))) t
    rw [sum_field k]
    fin_cases k
    · simpa [oscillatorField, oscillatorTrajectory, oscillatorCoordinate] using h
    · have hc := (Real.hasDerivAt_cos (t * u (some j))).comp t h
      simpa [Function.comp_def, oscillatorField, oscillatorTrajectory, oscillatorCoordinate,
        mul_comm] using hc
    · have hs := (Real.hasDerivAt_sin (t * u (some j))).comp t h
      simpa [Function.comp_def, oscillatorField, oscillatorTrajectory, oscillatorCoordinate,
        mul_comm] using hs

theorem oscillator_polynomial_derivative {n : ℕ} (u : OscillatorChannel n → ℝ)
    (t : ℝ) (p : OscillatorPolynomial n) :
    HasDerivAt (fun t => eval₂Hom (Int.castRingHom ℝ) (oscillatorTrajectory u t) p)
      (∑ i, u i * eval₂Hom (Int.castRingHom ℝ) (oscillatorTrajectory u t)
        (oscillatorDerivation i p)) t := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    simpa [← MvPolynomial.algebraMap_eq] using (hasDerivAt_const t (c : ℝ))
  | add p q hp hq =>
    have heq : (fun s => eval₂Hom (Int.castRingHom ℝ) (oscillatorTrajectory u s) (p + q)) =
        (fun s => eval₂Hom (Int.castRingHom ℝ) (oscillatorTrajectory u s) p) +
          (fun s => eval₂Hom (Int.castRingHom ℝ) (oscillatorTrajectory u s) q) := by
      funext s
      exact map_add (eval₂Hom (Int.castRingHom ℝ) (oscillatorTrajectory u s)) p q
    rw [heq]
    simpa only [map_add, mul_add, Finset.sum_add_distrib] using hp.add hq
  | mul_X p x hp =>
    let ev := eval₂Hom (Int.castRingHom ℝ) (oscillatorTrajectory u t)
    have hx := coordinate_derivative u t x
    have hp' := hp.mul hx
    simp only [map_mul]
    convert hp' using 1
    · funext s
      simp
    change (∑ i, u i * ev (oscillatorDerivation i (p * X x))) =
      (∑ i, u i * ev (oscillatorDerivation i p)) * oscillatorTrajectory u t x +
        ev p * (∑ i, u i * ev (oscillatorField i x))
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul]
    rw [show oscillatorDerivation i (X x) = oscillatorField i x from mkDerivation_X _ _ _]
    rw [show ev (X x) = oscillatorTrajectory u t x by simp [ev]]
    ring

def evaluationColumn {σ : Type*} [Fintype σ] [DecidableEq σ]
    (D : ℕ) (z : σ → ℝ) : State (Fintype.card (MonomialIndex σ D)) :=
  fun a => eval₂Hom (Int.castRingHom ℝ) z (basisMonomial D a)

def realOscillatorGenerator {n : ℕ} (D : ℕ) (u : OscillatorChannel n → ℝ) :
    RealMatrix (Fintype.card (MonomialIndex (OscillatorCoordinate n) D)) :=
  ∑ i, u i • (oscillatorMatrix D i).map (Int.castRingHom ℝ)

theorem evaluationColumn_oscillator_derivative {n : ℕ} (D : ℕ)
    (u : OscillatorChannel n → ℝ) (t : ℝ) :
    HasDerivAt (fun s => evaluationColumn D (oscillatorTrajectory u s))
      ((realOscillatorGenerator D u).mulVec (evaluationColumn D (oscillatorTrajectory u t))) t := by
  rw [hasDerivAt_pi]
  intro a
  have h := oscillator_polynomial_derivative u t (basisMonomial D a)
  convert h using 1
  · rfl
  change ∑ j, (realOscillatorGenerator D u) a j *
      evaluationColumn D (oscillatorTrajectory u t) j = _
  simp only [realOscillatorGenerator, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul, oscillatorMatrix, evaluationColumn]
  simp_rw [Finset.sum_mul, Finset.sum_comm (s := (Finset.univ : Finset
      (Fin (Fintype.card (MonomialIndex (OscillatorCoordinate n) D)))))]
  apply Finset.sum_congr rfl
  intro i _
  rw [derivative_row_expansion D _ (oscillator_row_degree D i), map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq, map_mul, eval₂Hom_C]
  ring

theorem evaluationColumn_oscillatorExp {n : ℕ} (D : ℕ) (u : OscillatorChannel n → ℝ) :
    (NormedSpace.exp (realOscillatorGenerator D u)).mulVec
      (evaluationColumn D fun x => (oscillatorBase n x : ℝ)) =
      evaluationColumn D (oscillatorTrajectory u 1) := by
  have h0 : evaluationColumn D (oscillatorTrajectory u 0) =
      evaluationColumn D (fun x => (oscillatorBase n x : ℝ)) := by
    exact congrArg (evaluationColumn D) (funext (oscillatorTrajectory_zero u))
  have h := eqOn_exp_mulVec_of_hasDerivWithinAt
    (realOscillatorGenerator D u) (evaluationColumn D (fun x => (oscillatorBase n x : ℝ)))
    (fun t => evaluationColumn D (oscillatorTrajectory u t)) 1 h0
    (fun t _ => (evaluationColumn_oscillator_derivative D u t).hasDerivWithinAt)
  simpa only [one_smul] using (h (show (1 : ℝ) ∈ Set.Icc 0 1 from ⟨zero_le_one, le_rfl⟩)).symm

end
end PolynomialLift
end ContinuousBilinear
