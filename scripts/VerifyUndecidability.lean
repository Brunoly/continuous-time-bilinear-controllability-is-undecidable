import ContinuousBilinear.IntegerReduction
import Hilbert10.Endpoints
import Lean.Util.CollectAxioms

namespace ContinuousBilinear

open Hilbert10

private theorem evalMonomialInt_eq_prod (n : ℕ) (powers : List ℕ) (x : List ℤ)
    (h : powers.length ≤ n) :
    PolynomialCode.evalMonomialInt powers x =
      ∏ i : Fin n, (x.getD i.val 0) ^ powers.getD i.val 0 := by
  induction n generalizing powers x with
  | zero =>
    have : powers = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h)
    subst powers
    simp
  | succ n ih =>
    cases powers with
    | nil => simp
    | cons e es =>
      have he : es.length ≤ n := by simpa using h
      cases x with
      | nil =>
        rw [Fin.prod_univ_succ]
        simpa [PolynomialCode.evalMonomialInt, List.getD] using
          congrArg ((0 : ℤ) ^ e * ·) (ih es [] he)
      | cons a as =>
        rw [Fin.prod_univ_succ]
        simpa [PolynomialCode.evalMonomialInt, List.getD] using
          congrArg (a ^ e * ·) (ih es as he)

/-- The polynomial evaluator of Hilbert10 agrees with the evaluation of the
finite Mathlib multivariate polynomial used by the reduction. -/
theorem evalInt_eq_denote_eval (p : IntegerPolynomialCode) (x : List ℤ) :
    (⟨p⟩ : PolynomialCode).evalInt x =
      MvPolynomial.eval (fun i : Fin p.arity => x.getD i.val 0) p.denote := by
  rw [IntegerPolynomialCode.denote, map_list_sum, List.map_map]
  unfold PolynomialCode.evalInt
  apply congrArg List.sum
  apply List.map_congr_left
  intro term ht
  have hb : term.2.length ≤ p.arity :=
    PolynomialCode.length_le_arity (p := ⟨p⟩) ht
  rw [evalMonomialInt_eq_prod p.arity term.2 x hb]
  simp

theorem intSolvable_iff_hasIntegerRoot (p : PolynomialCode) :
    IntSolvable p ↔ IntegerPolynomialCode.HasIntegerRoot p.terms := by
  have hEval (x : List ℤ) := evalInt_eq_denote_eval p.terms x
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨fun i => x.getD i.val 0, (hEval x).symm.trans hx⟩
  · rintro ⟨x, hx⟩
    refine ⟨List.ofFn x, ?_⟩
    have hGet : (fun i : Fin (IntegerPolynomialCode.arity p.terms) => (List.ofFn x).getD i.val 0) = x := by
      funext i
      rw [List.getD_eq_getElem _ _ (by simp)]
      simp
    rw [hEval, hGet]
    exact hx

theorem intSolvable_manyOneReducible_hasIntegerRoot :
    IntSolvable ≤₀ IntegerPolynomialCode.HasIntegerRoot :=
  ⟨PolynomialCode.terms, PolynomialCode.primrec_terms.to_comp, intSolvable_iff_hasIntegerRoot⟩

theorem integerHilbertTenth : Targets.IntegerHilbertTenth := by
  intro h
  exact Hilbert10.not_computablePred_intSolvable
    (ComputablePred.computable_of_manyOneReducible intSolvable_manyOneReducible_hasIntegerRoot h)

theorem canonicalIntegerUndecidability : Targets.CanonicalIntegerUndecidability :=
  canonicalIntegerUndecidability_of_reduction integerHilbertTenth integerReduction

theorem canonicalIntegerNoTotalDecider : Targets.CanonicalIntegerNoTotalDecider :=
  canonicalIntegerNoTotalDecider_of_undecidability canonicalIntegerUndecidability

theorem integerUndecidability : Targets.IntegerUndecidability :=
  integerUndecidability_of_reduction integerHilbertTenth integerReduction

theorem rationalUndecidability : Targets.RationalUndecidability :=
  rationalUndecidability_of_integer integerUndecidability integerToRationalTransport

theorem integrableIntegerUndecidability : Targets.IntegrableIntegerUndecidability :=
  integrableIntegerUndecidability_of_reduction integerHilbertTenth integerReductionWithIntegrableControls

theorem integrableRationalUndecidability : Targets.IntegrableRationalUndecidability :=
  integrableRationalUndecidability_of_integer integrableIntegerUndecidability

/-- Corollary 6.3 for any reachability relation induced by an intermediate
class of controls. -/
theorem intermediateControlUndecidability
    (Reachable : (P : Plant ℝ) → State P.dimension → State P.dimension → Prop)
    (hPC : ∀ (P : Plant ℝ) x y,
      (∃ M ∈ transitionMonoid P, M.mulVec x = y) → Reachable P x y)
    (hL1 : ∀ (P : Plant ℝ) x y,
      Reachable P x y → IntegrableControlReachable P x y) :
    (¬ ComputablePred (fun c : IntegerPlantCode =>
      c.WellFormed ∧ GloballyControllableFor (Reachable (toReal c.decode)))) ∧
    (¬ ComputablePred (fun c : RationalPlantCode =>
      c.WellFormed ∧ GloballyControllableFor (Reachable (toReal c.decode)))) ∧
    (¬ ∃ decide : IntegerPlantCode →. Bool, Partrec decide ∧
      ∀ c, CanonicalIntegerInstance c → ∃ b : Bool, b ∈ decide c ∧
        (b = true ↔ GloballyControllableFor (Reachable (toReal c.decode)))) :=
  intermediateControlUndecidability_of_reduction integerHilbertTenth
    integerReductionWithIntegrableControls Reachable hPC hL1

end ContinuousBilinear

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [`propext, `Classical.choice, `Quot.sound]
  let results := [``ContinuousBilinear.integerHilbertTenth,
    ``ContinuousBilinear.integerReduction, ``ContinuousBilinear.integerReductionWithIntegrableControls,
    ``ContinuousBilinear.canonicalIntegerUndecidability, ``ContinuousBilinear.canonicalIntegerNoTotalDecider,
    ``ContinuousBilinear.integerUndecidability, ``ContinuousBilinear.rationalUndecidability,
    ``ContinuousBilinear.integrableIntegerUndecidability, ``ContinuousBilinear.integrableRationalUndecidability,
    ``ContinuousBilinear.intermediateControlUndecidability]
  for name in results do
    let axioms := (← Lean.collectAxioms name).toList
    for ax in axioms do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    logInfo m!"{name} uses {axioms}"
