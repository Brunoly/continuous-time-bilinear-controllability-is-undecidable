import ContinuousBilinear.PolynomialLiftComputableDerivative
import ContinuousBilinear.CompilerRationalArithmeticProof

namespace ContinuousBilinear
namespace PolynomialLift

open MvPolynomial
open scoped BigOperators Matrix

/-- Dimension, generator tables, base column, output numerator row and denominator.
Matrix tables are lists of rows. Channel 0 is the affine direction. -/
abbrev FullPolynomialLiftCode := ℕ × List (List (List ℤ)) × List ℤ × List ℤ × ℤ

def signDegreeBoundCode (p : IntegerPolynomialCode) : ℕ := 2 * p.homogenizingDegreeCode + 2

@[simp] theorem signDegreeBoundCode_eq (p : IntegerPolynomialCode) :
    signDegreeBoundCode p = signDegreeBound p := by
  simp [signDegreeBoundCode, signDegreeBound, p.homogenizingDegreeCode_eq]

def signExponentsCode (p : IntegerPolynomialCode) : List (List ℕ) :=
  boundedExponentLists (signDegreeBoundCode p) (signCoordinateWidth p)

def generatorTable (p : IntegerPolynomialCode) (c : ℕ) : List (List ℤ) :=
  (signExponentsCode p).map fun row => (signExponentsCode p).map fun col =>
    monomialDerivativeEntry (p.arity + 1) c row col

def baseMonomialCode (p : IntegerPolynomialCode) (exps : List ℕ) : ℤ :=
  ((List.range (signCoordinateWidth p)).map fun i =>
    if i % 3 = 2 ∨ exps.getD i 0 = 0 then 1 else 0).prod

def signBaseValueCode (p : IntegerPolynomialCode) : ℤ := 144 * signScaleCode p ^ 2 + (-1)

@[simp] theorem signBaseValueCode_eq (p : IntegerPolynomialCode) :
    signBaseValueCode p = signBaseValue p := by simp [signBaseValueCode, signBaseValue, sub_eq_add_neg]

def compilePolynomialLift (p : IntegerPolynomialCode) : FullPolynomialLiftCode :=
  let exps := signExponentsCode p
  (exps.length, (List.range (p.arity + 2)).map (generatorTable p),
    exps.map (baseMonomialCode p),
    exps.map (fun a => SparseCode.coefficient (signPolynomialCode p) a),
    signBaseValueCode p)

private theorem primrec_signDegreeBoundCode : Primrec signDegreeBoundCode :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2)
    IntegerPolynomialCode.primrec_homogenizingDegreeCode) (Primrec.const 2)

private theorem primrec_signExponentsCode : Primrec signExponentsCode :=
  primrec_boundedExponentLists.comp primrec_signDegreeBoundCode primrec_signCoordinateWidth

private theorem primrec_int_listProd : Primrec (List.prod : List ℤ → ℤ) := by
  exact (Primrec.list_foldr Primrec.id (Primrec.const 1)
    (primrec_int_mul.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
      (fun a => by simp [List.prod_eq_foldr])

private theorem primrec_baseMonomialCode : Primrec₂ baseMonomialCode := by
  apply Primrec₂.curry.mp
  have hcos : PrimrecPred (fun a : (IntegerPolynomialCode × List ℕ) × ℕ => a.2 % 3 = 2) :=
    Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 3)) (Primrec.const 2)
  have hzero : PrimrecPred (fun a : (IntegerPolynomialCode × List ℕ) × ℕ =>
      a.1.2.getD a.2 0 = 0) :=
    Primrec.eq.comp ((Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
      (Primrec.const 0)
  exact primrec_int_listProd.comp (Primrec.list_map
    (Primrec.list_range.comp (primrec_signCoordinateWidth.comp Primrec.fst))
    (Primrec.ite (hcos.or hzero) (Primrec.const 1) (Primrec.const 0)).to₂)

private theorem primrec_generatorTable : Primrec₂ generatorTable := by
  apply Primrec₂.curry.mp
  have hrow : Primrec (fun a : (IntegerPolynomialCode × ℕ) × List ℕ =>
      (signExponentsCode a.1.1).map fun col =>
        monomialDerivativeEntry (a.1.1.arity + 1) a.1.2 a.2 col) := by
    apply Primrec.list_map (primrec_signExponentsCode.comp (Primrec.fst.comp Primrec.fst))
    let getP : Primrec (fun a : (((IntegerPolynomialCode × ℕ) × List ℕ) × List ℕ) => a.1.1.1) :=
      Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
    let getChannel : Primrec (fun a : (((IntegerPolynomialCode × ℕ) × List ℕ) × List ℕ) => a.1.1.2) :=
      Primrec.snd.comp (Primrec.fst.comp Primrec.fst)
    exact (primrec_monomialDerivativeEntry.comp
      ((Primrec.succ.comp (IntegerPolynomialCode.primrec_arity.comp getP)).pair
        (getChannel.pair ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)))).to₂
  exact Primrec.list_map (primrec_signExponentsCode.comp Primrec.fst) hrow.to₂

private theorem primrec_signBaseValueCode : Primrec signBaseValueCode := by
  have hs : Primrec signScaleCode :=
    IntegerPolynomialCode.primrec_signScale.of_eq (fun p => (signScaleCode_eq p).symm)
  exact (primrec_int_add.comp
    (primrec_int_mul.comp (Primrec.const 144) (primrec_int_mul.comp hs hs))
      (Primrec.const (-1))).of_eq (fun p => by simp [signBaseValueCode, pow_two])

theorem primrec_compilePolynomialLift : Primrec compilePolynomialLift := by
  exact (Primrec.list_length.comp primrec_signExponentsCode).pair
    ((Primrec.list_map (Primrec.list_range.comp
      (Primrec.nat_add.comp IntegerPolynomialCode.primrec_arity (Primrec.const 2))) primrec_generatorTable).pair
      ((Primrec.list_map primrec_signExponentsCode primrec_baseMonomialCode).pair
        ((Primrec.list_map primrec_signExponentsCode
          (SparseCode.primrec_coefficient.comp (primrec_signPolynomialCode.comp Primrec.fst)
            Primrec.snd).to₂).pair primrec_signBaseValueCode)))

private noncomputable def codeExponentIndex (p : IntegerPolynomialCode) :
    Fin (signExponentsCode p).length ≃
      MonomialIndex (SignCoordinate p) (signDegreeBound p) :=
  (oscillatorExponentIndex (signDegreeBoundCode p) (p.arity + 1)).trans {
    toFun a := ⟨a.val, (signDegreeBoundCode_eq p) ▸ a.property⟩
    invFun a := ⟨a.val, (signDegreeBoundCode_eq p).symm ▸ a.property⟩
    left_inv _ := Subtype.ext rfl
    right_inv _ := Subtype.ext rfl }

noncomputable def liftIndexEquiv (p : IntegerPolynomialCode) :
    Fin (signExponentsCode p).length ≃ Fin (signDimension p) :=
  (codeExponentIndex p).trans
    (monomialIndexEquiv (SignCoordinate p) (signDegreeBound p)).symm

theorem liftIndexEquiv_exponents (p : IntegerPolynomialCode)
    (i : Fin (signExponentsCode p).length) :
    (monomialIndexEquiv (SignCoordinate p) (signDegreeBound p) (liftIndexEquiv p i)).val =
      exponentListOn (p.arity + 1) ((signExponentsCode p).get i) := by
  have hback :
      monomialIndexEquiv (SignCoordinate p) (signDegreeBound p) (liftIndexEquiv p i) =
        codeExponentIndex p i :=
    (monomialIndexEquiv (SignCoordinate p) (signDegreeBound p)).apply_symm_apply _
  rw [hback]
  ext x
  rw [exponentListOn_apply]
  exact oscillatorExponentIndex_apply _ _ i x

theorem generatorTable_entry (p : IntegerPolynomialCode) (c : Fin (p.arity + 2))
    (i j : Fin (signExponentsCode p).length) :
    monomialDerivativeEntry (p.arity + 1) c.val ((signExponentsCode p).get i)
      ((signExponentsCode p).get j) =
      signMatrices p (oscillatorChannelAt (p.arity + 1) c) (liftIndexEquiv p i) (liftIndexEquiv p j) := by
  have hlen := (mem_boundedExponentLists _ _ _).mp (List.get_mem (signExponentsCode p) j)
  rw [monomialDerivativeEntry_eq_coeff _ c _ _ hlen.1]
  unfold signMatrices oscillatorMatrix evaluationMatrix basisMonomial
  rw [liftIndexEquiv_exponents, liftIndexEquiv_exponents]

theorem outputNumerator_entry (p : IntegerPolynomialCode) (j : Fin (signExponentsCode p).length) :
    SparseCode.coefficient (signPolynomialCode p) ((signExponentsCode p).get j) =
      (signPolynomial p).coeff
        (monomialIndexEquiv (SignCoordinate p) (signDegreeBound p) (liftIndexEquiv p j)).val := by
  have hlen := (mem_boundedExponentLists _ _ _).mp (List.get_mem (signExponentsCode p) j)
  rw [liftIndexEquiv_exponents, ← denoteOn_signPolynomialCode]
  exact (coeff_denoteOn_eq_sparseCoefficient _ _ (wellSized_signPolynomialCode p) _ hlen.1).symm

private theorem oscillatorBase_number {n : ℕ} (x : OscillatorCoordinate n) :
    oscillatorBase n x = if (oscillatorCoordinateNumber x).val % 3 = 2 then 1 else 0 := by
  rcases x with _ | ⟨i, k⟩
  · simp [oscillatorBase, oscillatorCoordinateNumber]
  · fin_cases k <;> simp [oscillatorBase, oscillatorCoordinateNumber, Nat.add_mod]

theorem baseMonomial_entry (p : IntegerPolynomialCode) (j : Fin (signExponentsCode p).length) :
    baseMonomialCode p ((signExponentsCode p).get j) =
      signInitialVector p (liftIndexEquiv p j) := by
  unfold baseMonomialCode signInitialVector basisMonomial
  rw [liftIndexEquiv_exponents, MvPolynomial.eval_monomial, one_mul, Finsupp.prod_pow]
  unfold signCoordinateWidth
  rw [← SparseCode.ofFn_val_map_range, List.prod_ofFn]
  refine Fintype.prod_equiv (oscillatorCoordinateEquiv (p.arity + 1)).symm _ _ ?_
  intro i
  have hi : oscillatorCoordinateNumber ((oscillatorCoordinateEquiv (p.arity + 1)).symm i) = i :=
    (oscillatorCoordinateEquiv (p.arity + 1)).apply_symm_apply i
  rw [exponentListOn_apply, oscillatorBase_number, hi]
  by_cases hc : i.val % 3 = 2
  · simp [hc]
  · by_cases he : ((signExponentsCode p).get j).getD i.val 0 = 0
    · simp only [hc, he, false_or, ite_true, ite_false, pow_zero]
    · simp only [hc, he, false_or, ite_false, zero_pow he]

/-- Generator matrices decoded from the finite tables in their enumeration order. -/
def compiledSignMatrices (p : IntegerPolynomialCode) (c : Fin (p.arity + 2)) :
    Matrix (Fin (compilePolynomialLift p).1) (Fin (compilePolynomialLift p).1) ℤ :=
  fun i j => ((((compilePolynomialLift p).2.1.getD c.val []).getD i.val []).getD j.val 0)

def compiledSignInitial (p : IntegerPolynomialCode) : Fin (compilePolynomialLift p).1 → ℤ :=
  fun i => (compilePolynomialLift p).2.2.1.getD i.val 0

def compiledSignOutput (p : IntegerPolynomialCode) : Fin (compilePolynomialLift p).1 → ℚ :=
  fun i => ((compilePolynomialLift p).2.2.2.1.getD i.val 0 : ℚ) /
    ((compilePolynomialLift p).2.2.2.2 : ℚ)

theorem compiledSignMatrices_entry (p : IntegerPolynomialCode) (c : Fin (p.arity + 2))
    (i j : Fin (compilePolynomialLift p).1) :
    compiledSignMatrices p c i j =
      signMatrices p (oscillatorChannelAt (p.arity + 1) c) (liftIndexEquiv p i) (liftIndexEquiv p j) := by
  change Fin (signExponentsCode p).length at i j
  have hi : i.val < (signExponentsCode p).length := i.isLt
  have hj : j.val < (signExponentsCode p).length := j.isLt
  simpa only [compiledSignMatrices, compilePolynomialLift, generatorTable,
    List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range c.isLt,
    getElem?_pos (signExponentsCode p) i.val hi, getElem?_pos (signExponentsCode p) j.val hj, Option.map_some, Option.getD_some,
    List.get_eq_getElem] using generatorTable_entry p c i j

theorem compiledSignInitial_entry (p : IntegerPolynomialCode) (i : Fin (compilePolynomialLift p).1) :
    compiledSignInitial p i = signInitialVector p (liftIndexEquiv p i) := by
  change Fin (signExponentsCode p).length at i
  have hi : i.val < (signExponentsCode p).length := i.isLt
  simpa only [compiledSignInitial, compilePolynomialLift, List.getD_eq_getElem?_getD,
    List.getElem?_map, getElem?_pos (signExponentsCode p) i.val hi, Option.map_some, Option.getD_some, List.get_eq_getElem] using
    baseMonomial_entry p i

theorem compiledSignOutput_entry (p : IntegerPolynomialCode) (i : Fin (compilePolynomialLift p).1) :
    compiledSignOutput p i = signOutputRow p (liftIndexEquiv p i) := by
  change Fin (signExponentsCode p).length at i
  have hi : i.val < (signExponentsCode p).length := i.isLt
  simp only [compiledSignOutput, compilePolynomialLift, List.getD_eq_getElem?_getD, List.getElem?_map,
    getElem?_pos (signExponentsCode p) i.val hi, Option.map_some, Option.getD_some, signBaseValueCode_eq, signOutputRow]
  have hnum := outputNumerator_entry p i
  simpa only [List.get_eq_getElem] using
    congrArg (fun a : ℤ => (a : ℚ) / (signBaseValue p : ℚ)) hnum

end PolynomialLift
end ContinuousBilinear
