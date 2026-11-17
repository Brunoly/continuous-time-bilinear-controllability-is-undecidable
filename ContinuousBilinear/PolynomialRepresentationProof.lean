import ContinuousBilinear.PolynomialLiftDynamics
import ContinuousBilinear.SignEncodingProof

namespace ContinuousBilinear
namespace PolynomialLift

open MvPolynomial
open scoped BigOperators Matrix

noncomputable section

abbrev SignCoordinate (p : IntegerPolynomialCode) := OscillatorCoordinate (p.arity + 1)
abbrev SignChannel (p : IntegerPolynomialCode) := OscillatorChannel (p.arity + 1)
abbrev SignPolynomial (p : IntegerPolynomialCode) := MvPolynomial (SignCoordinate p) ℤ

def position {p : IntegerPolynomialCode} (i : Fin (p.arity + 1)) : SignPolynomial p :=
  X (oscillatorCoordinate i 0)

def sineCoordinate {p : IntegerPolynomialCode} (i : Fin (p.arity + 1)) : SignPolynomial p :=
  X (oscillatorCoordinate i 2)

def affineVariable (p : IntegerPolynomialCode) : SignPolynomial p := X affineCoordinate

def homogenizedPolynomial (p : IntegerPolynomialCode) : SignPolynomial p :=
  ∑ a ∈ p.denote.support, C (p.denote.coeff a) *
    (position (p := p) 0) ^ (p.homogenizingDegree - a.sum (fun _ e => e)) *
    ∏ i : Fin p.arity, (position (p := p) i.succ) ^ a i

def gatePolynomial (p : IntegerPolynomialCode) : SignPolynomial p :=
  (position (p := p) 0 - C 3) * (C 4 - position (p := p) 0) - affineVariable p ^ 2

def signPolynomial (p : IntegerPolynomialCode) : SignPolynomial p :=
  homogenizedPolynomial p ^ 2 + C (p.signScale ^ 2) *
    (1 + ∑ i, position (p := p) i ^ 2) ^ (p.homogenizingDegree - 1) *
    ((∑ i, sineCoordinate (p := p) i ^ 2) + gatePolynomial p ^ 2) - 1

def signDegreeBound (p : IntegerPolynomialCode) : ℕ := 2 * p.homogenizingDegree + 2

theorem totalDegree_homogenizedPolynomial (p : IntegerPolynomialCode) :
    (homogenizedPolynomial p).totalDegree ≤ p.homogenizingDegree := by
  unfold homogenizedPolynomial
  apply totalDegree_finsetSum_le
  intro a ha
  have ha' := (MvPolynomial.le_totalDegree ha).trans (le_max_right 1 p.denote.totalDegree)
  change a.sum (fun _ e => e) ≤ p.homogenizingDegree at ha'
  have hprod : (∏ i : Fin p.arity, position (p := p) i.succ ^ a i).totalDegree ≤
      a.sum (fun _ e => e) := by
    rw [sum_exponents]
    simpa only [position, totalDegree_X_pow, monomialDegree] using
      (totalDegree_finsetProd Finset.univ (fun i : Fin p.arity => position (p := p) i.succ ^ a i))
  have hfirst : (C (p.denote.coeff a) *
      position (p := p) 0 ^ (p.homogenizingDegree - a.sum (fun _ e => e))).totalDegree ≤
      p.homogenizingDegree - a.sum (fun _ e => e) := by
    simpa only [totalDegree_C, position, totalDegree_X_pow, zero_add] using
      (totalDegree_mul (C (p.denote.coeff a) : SignPolynomial p)
        (position (p := p) 0 ^ (p.homogenizingDegree - a.sum (fun _ e => e))))
  exact ((totalDegree_mul _ _).trans (Nat.add_le_add hfirst hprod)).trans
    (Nat.sub_add_cancel ha').le

theorem totalDegree_gatePolynomial (p : IntegerPolynomialCode) :
    (gatePolynomial p).totalDegree ≤ 2 := by
  unfold gatePolynomial
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · have h₁ : (position (p := p) 0 - C 3).totalDegree ≤ 1 :=
      (totalDegree_sub _ _).trans (max_le (by simp [position, totalDegree_X])
        ((totalDegree_C (σ := SignCoordinate p) (3 : ℤ)).le.trans (Nat.zero_le 1)))
    have h₂ : (C 4 - position (p := p) 0).totalDegree ≤ 1 :=
      (totalDegree_sub _ _).trans (max_le
        ((totalDegree_C (σ := SignCoordinate p) (4 : ℤ)).le.trans (Nat.zero_le 1))
        (by simp [position, totalDegree_X]))
    exact (totalDegree_mul _ _).trans (Nat.add_le_add h₁ h₂)
  · simp [affineVariable]

theorem totalDegree_signPolynomial (p : IntegerPolynomialCode) :
    (signPolynomial p).totalDegree ≤ signDegreeBound p := by
  let d := p.homogenizingDegree
  have hd : 1 ≤ d := le_max_left _ _
  have hQ := (totalDegree_pow (homogenizedPolynomial p) 2).trans
    (Nat.mul_le_mul_left 2 (totalDegree_homogenizedPolynomial p))
  have hRsum : (∑ i, position (p := p) i ^ 2).totalDegree ≤ 2 :=
    totalDegree_finsetSum_le (by intro i _; simp [position])
  have hR : (1 + ∑ i, position (p := p) i ^ 2).totalDegree ≤ 2 :=
    (totalDegree_add _ _).trans (max_le (by simp [totalDegree_one]) hRsum)
  have hRpow : ((1 + ∑ i, position (p := p) i ^ 2) ^ (d - 1)).totalDegree ≤ (d - 1) * 2 :=
    (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ hR)
  have hSsum : (∑ i, sineCoordinate (p := p) i ^ 2).totalDegree ≤ 2 :=
    totalDegree_finsetSum_le (by intro i _; simp [sineCoordinate])
  have hgsq : (gatePolynomial p ^ 2).totalDegree ≤ 4 :=
    (totalDegree_pow _ 2).trans (Nat.mul_le_mul_left 2 (totalDegree_gatePolynomial p))
  have hS : ((∑ i, sineCoordinate (p := p) i ^ 2) + gatePolynomial p ^ 2).totalDegree ≤ 4 :=
    (totalDegree_add _ _).trans (max_le (hSsum.trans (by decide)) hgsq)
  have hC : (C (p.signScale ^ 2) : SignPolynomial p).totalDegree ≤ 0 :=
    (totalDegree_C _).le
  have hW := (totalDegree_mul (C (p.signScale ^ 2) : SignPolynomial p) _).trans
    (Nat.add_le_add hC hRpow)
  have hW' := (totalDegree_mul (C (p.signScale ^ 2) *
    (1 + ∑ i, position (p := p) i ^ 2) ^ (d - 1)) _).trans (Nat.add_le_add hW hS)
  unfold signPolynomial signDegreeBound
  refine (totalDegree_sub _ _).trans (max_le ?_ (by simp [totalDegree_one]))
  exact (totalDegree_add _ _).trans (max_le (hQ.trans (by omega)) (hW'.trans (by omega)))

theorem eval_signPolynomial (p : IntegerPolynomialCode) (z : SignCoordinate p → ℝ) :
    eval₂Hom (Int.castRingHom ℝ) z (signPolynomial p) =
      p.signPolynomialValue (fun i => z (oscillatorCoordinate i 0))
        (fun i => z (oscillatorCoordinate i 2)) (z affineCoordinate) := by
  have he (c : ℤ) : eval₂ (Int.castRingHom ℝ) z (c : SignPolynomial p) = (c : ℝ) :=
    map_intCast (eval₂Hom (Int.castRingHom ℝ) z) c
  simp [signPolynomial, homogenizedPolynomial, gatePolynomial, IntegerPolynomialCode.signPolynomialValue,
    IntegerPolynomialCode.homogenizedValue, position, sineCoordinate, affineVariable, he]

def signBaseValue (p : IntegerPolynomialCode) : ℤ := 144 * p.signScale ^ 2 - 1

theorem signBaseValue_pos (p : IntegerPolynomialCode) : 0 < (signBaseValue p) := by
  have hd : 0 < p.homogenizingDegree := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hs : 0 < p.signScale := by
    unfold IntegerPolynomialCode.signScale IntegerPolynomialCode.coefficientHeight
    positivity
  have hs' : 1 ≤ p.signScale := by omega
  have hsq : 1 ≤ p.signScale ^ 2 := by
    simpa using pow_le_pow_left₀ (show (0 : ℤ) ≤ 1 by decide) hs' 2
  unfold signBaseValue
  linarith

theorem eval_signPolynomial_base (p : IntegerPolynomialCode) :
    eval₂Hom (Int.castRingHom ℝ) (fun z => (oscillatorBase (p.arity + 1) z : ℝ))
      (signPolynomial p) = ((signBaseValue p) : ℝ) := by
  rw [eval_signPolynomial]
  have hzero : p.homogenizedValue (fun _ => 0) = 0 := by
    have h := p.homogenizedValue_integerRay 0 (fun _ => 0)
    have hd : p.homogenizingDegree ≠ 0 :=
      Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
    have hc : (Fin.cases (0 : ℝ) (fun _ : Fin p.arity => (0 : ℝ))) = fun _ => 0 := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp
    have hp0 : (0 : ℝ) ^ p.homogenizingDegree = 0 := zero_pow hd
    simpa only [Int.cast_zero, mul_zero, hc, hp0, zero_mul] using h
  simp [oscillatorBase, oscillatorCoordinate, affineCoordinate, signBaseValue,
    IntegerPolynomialCode.signPolynomialValue, hzero]
  ring

def signDimension (p : IntegerPolynomialCode) : ℕ :=
  Fintype.card (MonomialIndex (SignCoordinate p) (signDegreeBound p))

def signMatrices (p : IntegerPolynomialCode) (i : SignChannel p) :
    Matrix (Fin (signDimension p)) (Fin (signDimension p)) ℤ :=
  oscillatorMatrix (signDegreeBound p) i

def signInitialVector (p : IntegerPolynomialCode) : Fin (signDimension p) → ℤ :=
  fun j => eval (oscillatorBase (p.arity + 1)) (basisMonomial (signDegreeBound p) j)

def signOutputRow (p : IntegerPolynomialCode) : Fin (signDimension p) → ℚ :=
  fun j => ((signPolynomial p).coeff
    (monomialIndexEquiv (SignCoordinate p) (signDegreeBound p) j).val : ℚ) / (signBaseValue p)

theorem commute_signMatrices (p : IntegerPolynomialCode) (i j : SignChannel p) :
    Commute ((signMatrices p) i) ((signMatrices p) j) := commute_oscillatorMatrix _ _ _

theorem signInitialVector_cast (p : IntegerPolynomialCode) :
    (fun j => ((signInitialVector p) j : ℝ)) =
      evaluationColumn (signDegreeBound p) (fun z => (oscillatorBase (p.arity + 1) z : ℝ)) := by
  funext j
  unfold signInitialVector evaluationColumn
  induction (basisMonomial (signDegreeBound p) j : SignPolynomial p)
      using MvPolynomial.induction_on with
  | C c => simp
  | add f g hf hg => simp [hf, hg]
  | mul_X f x hf => simp [hf]

theorem signOutputRow_eval (p : IntegerPolynomialCode) (z : SignCoordinate p → ℝ) :
    (∑ j, ((signOutputRow p) j : ℝ) * evaluationColumn (signDegreeBound p) z j) =
      eval₂Hom (Int.castRingHom ℝ) z (signPolynomial p) / ((signBaseValue p) : ℝ) := by
  have h := congrArg (eval₂Hom (Int.castRingHom ℝ) z)
    (bounded_monomial_expansion (signDegreeBound p) _ (totalDegree_signPolynomial p))
  simp only [map_sum, Algebra.smul_def, MvPolynomial.algebraMap_eq, map_mul, eval₂Hom_C] at h
  unfold signOutputRow evaluationColumn
  rw [h, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [Rat.cast_div]
  push_cast
  simp only [Int.coe_castRingHom]
  ring

/-- The coefficient row and base monomial column are normalized by the value at the base. -/
theorem signOutput_initial (p : IntegerPolynomialCode) :
    (∑ j, ((signOutputRow p) j : ℝ) * ((signInitialVector p) j : ℝ)) = 1 := by
  simp_rw [congrFun (signInitialVector_cast p)]
  rw [signOutputRow_eval, eval_signPolynomial_base]
  exact div_self (by exact_mod_cast (signBaseValue_pos p).ne')

/-- The exact scalar polynomial representation in the monomial evaluation convention. -/
theorem signPolynomial_matrix_coefficient (p : IntegerPolynomialCode) (u : SignChannel p → ℝ) :
    (∑ j, ((signOutputRow p) j : ℝ) *
      ((NormedSpace.exp (∑ i, u i • ((signMatrices p) i).map (Int.castRingHom ℝ))).mulVec
        (fun j => ((signInitialVector p) j : ℝ))) j) =
      p.signPolynomialValue (fun i => u (some i)) (fun i => Real.sin (u (some i))) (u none) /
        ((signBaseValue p) : ℝ) := by
  rw [signInitialVector_cast]
  change (∑ j, ((signOutputRow p) j : ℝ) *
    ((NormedSpace.exp (realOscillatorGenerator (signDegreeBound p) u)).mulVec _) j) = _
  rw [evaluationColumn_oscillatorExp, signOutputRow_eval, eval_signPolynomial]
  simp [oscillatorTrajectory, oscillatorCoordinate, affineCoordinate]

/-- A negative exponential coefficient exists exactly when the input polynomial has an integer root. -/
theorem signPolynomial_negative_matrix_coefficient_iff (p : IntegerPolynomialCode) :
    (∃ u : SignChannel p → ℝ, (∑ j, ((signOutputRow p) j : ℝ) *
      ((NormedSpace.exp (∑ i, u i • ((signMatrices p) i).map (Int.castRingHom ℝ))).mulVec
        (fun j => ((signInitialVector p) j : ℝ))) j) < 0) ↔ p.HasIntegerRoot := by
  have hpos : 0 < (signBaseValue p : ℝ) := by exact_mod_cast signBaseValue_pos p
  constructor
  · rintro ⟨u, hu⟩
    rw [signPolynomial_matrix_coefficient] at hu
    apply p.hasIntegerRoot_of_negative (fun i => u (some i)) (u none)
    simpa only [zero_mul] using (div_lt_iff₀ hpos).mp hu
  · intro hp
    obtain ⟨q, a, ha⟩ := p.exists_negative_of_hasIntegerRoot hp
    refine ⟨fun i => i.elim a q, ?_⟩
    rw [signPolynomial_matrix_coefficient]
    apply (div_lt_iff₀ hpos).mpr
    simpa only [zero_mul, Option.elim_some, Option.elim_none] using ha

end
end PolynomialLift
end ContinuousBilinear

