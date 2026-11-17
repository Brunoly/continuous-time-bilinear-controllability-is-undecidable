import ContinuousBilinear.PolynomialLift
import Mathlib.Algebra.MvPolynomial.CommRing

namespace ContinuousBilinear
namespace PolynomialLift

open MvPolynomial
open scoped BigOperators Matrix

noncomputable section

/-- The affine coordinate, followed by the position, cosine and sine of each oscillator. -/
abbrev OscillatorCoordinate (n : ℕ) := Unit ⊕ (Fin n × Fin 3)

abbrev OscillatorChannel (n : ℕ) := Option (Fin n)

abbrev OscillatorPolynomial (n : ℕ) := MvPolynomial (OscillatorCoordinate n) ℤ

def affineCoordinate {n : ℕ} : OscillatorCoordinate n := Sum.inl ()

def oscillatorCoordinate {n : ℕ} (i : Fin n) (k : Fin 3) : OscillatorCoordinate n :=
  Sum.inr (i, k)

def oscillatorField {n : ℕ} (i : OscillatorChannel n) (x : OscillatorCoordinate n) :
    OscillatorPolynomial n :=
  match i, x with
  | none, .inl _ => 1
  | none, .inr _ => 0
  | some _, .inl _ => 0
  | some i, .inr (j, k) =>
    if i = j then
      if k = 0 then 1 else if k = 1 then -X (oscillatorCoordinate i 2)
      else X (oscillatorCoordinate i 1)
    else 0

def oscillatorDerivation {n : ℕ} (i : OscillatorChannel n) :
    Derivation ℤ (OscillatorPolynomial n) (OscillatorPolynomial n) :=
  mkDerivation ℤ (oscillatorField i)

theorem totalDegree_oscillatorField {n : ℕ} (i : OscillatorChannel n)
    (x : OscillatorCoordinate n) : (oscillatorField i x).totalDegree ≤ 1 := by
  cases i <;> cases x
  · simp [oscillatorField]
  · simp [oscillatorField]
  · simp [oscillatorField]
  · rename_i i y
    obtain ⟨j, k⟩ := y
    fin_cases k <;> by_cases h : i = j <;> simp [oscillatorField, h, totalDegree_X, totalDegree_neg]

private def derivationCommutator {n : ℕ}
    (V W : Derivation ℤ (OscillatorPolynomial n) (OscillatorPolynomial n)) :
    Derivation ℤ (OscillatorPolynomial n) (OscillatorPolynomial n) :=
  Derivation.mk' (V.toLinearMap.comp W.toLinearMap - W.toLinearMap.comp V.toLinearMap) (by
    intro a b
    change V (W (a * b)) - W (V (a * b)) =
      a • (V (W b) - W (V b)) + b • (V (W a) - W (V a))
    simp only [Derivation.leibniz, smul_eq_mul, map_add]
    ring)

theorem oscillatorDerivation_commute {n : ℕ} (i j : OscillatorChannel n)
    (p : OscillatorPolynomial n) :
    oscillatorDerivation i (oscillatorDerivation j p) =
      oscillatorDerivation j (oscillatorDerivation i p) := by
  suffices h : derivationCommutator (oscillatorDerivation i) (oscillatorDerivation j) = 0 by
    have h' := congrArg (fun D : Derivation ℤ (OscillatorPolynomial n)
      (OscillatorPolynomial n) => D p) h
    change oscillatorDerivation i (oscillatorDerivation j p) -
      oscillatorDerivation j (oscillatorDerivation i p) = 0 at h'
    exact sub_eq_zero.mp h'
  by_cases hij : i = j
  · subst j
    apply MvPolynomial.derivation_ext
    intro x
    exact sub_self (oscillatorDerivation i (oscillatorDerivation i (X x)))
  apply MvPolynomial.derivation_ext
  intro x
  change oscillatorDerivation i (oscillatorDerivation j (X x)) -
    oscillatorDerivation j (oscillatorDerivation i (X x)) = 0
  simp only [sub_eq_zero, oscillatorDerivation, mkDerivation_X]
  change mkDerivation ℤ (oscillatorField i) (oscillatorField j x) =
    mkDerivation ℤ (oscillatorField j) (oscillatorField i x)
  rcases i with _ | i <;> rcases j with _ | j <;> rcases x with x | ⟨k, l⟩
  · exact False.elim (hij rfl)
  · exact False.elim (hij rfl)
  · simp [oscillatorField]
  · fin_cases l <;> by_cases h : j = k <;>
      simp [oscillatorField, h, oscillatorCoordinate, mkDerivation_X]
  · simp [oscillatorField]
  · fin_cases l <;> by_cases h : i = k <;>
      simp [oscillatorField, h, oscillatorCoordinate, mkDerivation_X]
  · simp [oscillatorField]
  · have hne : i ≠ j := fun h => hij (congrArg some h)
    fin_cases l <;> by_cases hi : i = k <;> by_cases hj : j = k <;>
      simp_all [oscillatorField, oscillatorCoordinate, mkDerivation_X]

def oscillatorMatrix {n : ℕ} (D : ℕ) (i : OscillatorChannel n) :=
  evaluationMatrix D (oscillatorDerivation i)

theorem oscillator_row_degree {n : ℕ} (D : ℕ) (i : OscillatorChannel n)
    (a : Fin (Fintype.card (MonomialIndex (OscillatorCoordinate n) D))) :
    (oscillatorDerivation i (basisMonomial D a)).totalDegree ≤ D :=
  (affine_derivation_monomial_degree (oscillatorField i) (totalDegree_oscillatorField i)
    (monomialIndexEquiv (OscillatorCoordinate n) D a).val).trans
    (monomialIndexEquiv (OscillatorCoordinate n) D a).property

/-- Integer matrices acting on columns of monomial values for independent oscillators. -/
theorem commute_oscillatorMatrix {n : ℕ} (D : ℕ) (i j : OscillatorChannel n) :
    Commute (oscillatorMatrix D i) (oscillatorMatrix D j) :=
  commute_evaluationMatrix D _ _ (oscillator_row_degree D i)
    (oscillator_row_degree D j) (oscillatorDerivation_commute i j)

end
end PolynomialLift
end ContinuousBilinear
