import ContinuousBilinear.CompilerFeedbackCodeProof
import ContinuousBilinear.CompilerListFoldProof
import ContinuousBilinear.CompilerWordExponentialProof

namespace ContinuousBilinear.RationalFeedbackCode

open PolynomialLift

private def matrixEntry (c : RationalFeedbackCode) (k i j : ℕ) : ℚ :=
  (c.2.2.2.getD k []).getD (i * c.1 + j) 0

private def applyOperator (c : RationalFeedbackCode) (k : ℕ) (v : List ℚ) : List ℚ :=
  (List.range c.1).map fun i =>
    ((List.range c.1).map fun j => matrixEntry c k i j * v.getD j 0).sum

/-- The rational output coefficient of a finite sequence of control matrices. -/
def wordOutput (c : RationalFeedbackCode) (w : List ℕ) : ℚ :=
  let v := w.foldr (applyOperator c) c.2.1
  ((List.range c.1).map fun j => c.2.2.1.getD j 0 * v.getD j 0).sum

private theorem getD_computable {α β : Type*} [Primcodable α] [Primcodable β]
    {xs : α → List β} {i : α → ℕ} (hxs : Computable xs) (hi : Computable i) (z : β) :
    Computable fun a => (xs a).getD (i a) z :=
  (Primrec.option_getD.to_comp.comp (Computable.list_getElem?.comp hxs hi)
    (Computable.const z)).of_eq fun _ => rfl

private theorem computable_matrixEntry :
    Computable fun p : (RationalFeedbackCode × ℕ) × ℕ × ℕ =>
      matrixEntry p.1.1 p.1.2 p.2.1 p.2.2 := by
  let hc : Computable (fun p : (RationalFeedbackCode × ℕ) × ℕ × ℕ => p.1.1) :=
    Computable.fst.comp Computable.fst
  let hk : Computable (fun p : (RationalFeedbackCode × ℕ) × ℕ × ℕ => p.1.2) :=
    Computable.snd.comp Computable.fst
  let hi : Computable (fun p : (RationalFeedbackCode × ℕ) × ℕ × ℕ => p.2.1) :=
    Computable.fst.comp Computable.snd
  let hj : Computable (fun p : (RationalFeedbackCode × ℕ) × ℕ × ℕ => p.2.2) :=
    Computable.snd.comp Computable.snd
  exact getD_computable
    (getD_computable (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hc))) hk [])
    (Primrec.nat_add.to_comp.comp
      (Primrec.nat_mul.to_comp.comp hi (Computable.fst.comp hc)) hj) 0

private theorem computable_applyOperator : Computable₂ fun c (p : ℕ × List ℚ) =>
    applyOperator c p.1 p.2 := by
  change Computable fun p : RationalFeedbackCode × ℕ × List ℚ => applyOperator p.1 p.2.1 p.2.2
  unfold applyOperator
  apply computable_list_map (Primrec.list_range.to_comp.comp (Computable.fst.comp Computable.fst))
  apply computable_rational_sum_range
    (Computable.fst.comp (Computable.fst.comp Computable.fst))
  let P := ((RationalFeedbackCode × ℕ × List ℚ) × ℕ) × ℕ
  have hdata : Computable (fun p : P => p.1.1) := Computable.fst.comp Computable.fst
  have hrow : Computable (fun p : P => p.1.2) := Computable.snd.comp Computable.fst
  have hcol : Computable (fun p : P => p.2) := Computable.snd
  have hc : Computable (fun p : P => ((p.1.1.1, p.1.1.2.1), p.1.2, p.2)) :=
    ((Computable.fst.comp hdata).pair (Computable.fst.comp (Computable.snd.comp hdata))).pair
      (hrow.pair hcol)
  exact (computable_rat_mul.comp (computable_matrixEntry.comp hc)
    (getD_computable (Computable.snd.comp (Computable.snd.comp hdata)) hcol 0)).to₂

theorem computable_wordOutput : Computable₂ wordOutput := by
  change Computable fun p : RationalFeedbackCode × List ℕ => wordOutput p.1 p.2
  let P := RationalFeedbackCode × List ℕ
  let step (p : P) (q : ℕ × List ℚ) := applyOperator p.1 q.1 q.2
  have hstep0 := computable_applyOperator.comp
    (Computable.fst.comp Computable.fst : Computable (fun p : P × ℕ × List ℚ => p.1.1))
    (Computable.snd : Computable (fun p : P × ℕ × List ℚ => p.2))
  have hstep : Computable₂ step := (hstep0.of_eq (g := Function.uncurry step)
    (fun _ => rfl)).to₂
  have hinit : Computable (fun p : P => p.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have heval := computable_list_foldr (step := step) 0
    (Computable.snd : Computable (fun p : P => p.2)) hinit hstep
  unfold wordOutput
  apply computable_rational_sum_range (Computable.fst.comp Computable.fst)
  have hout : Computable (fun p : (RationalFeedbackCode × List ℕ) × ℕ => p.1.1.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.fst)))
  exact (computable_rat_mul.comp (getD_computable hout Computable.snd 0)
    (getD_computable (heval.comp Computable.fst) Computable.snd 0)).to₂

/-- The underlying linear representation on the rational coordinate space. -/
def representation (c : RationalFeedbackCode) :
    LinearRepresentation ℚ (Fin c.1 → ℚ) (Fin c.2.2.2.length) where
  operator k := Matrix.mulVecLin (c.operator k)
  initial := c.initial
  output := { toFun := fun x => dotProduct c.output x
              map_add' := fun _ _ => dotProduct_add _ _ _
              map_smul' := fun a _ => dotProduct_smul a _ _ }

private theorem sum_range_eq_sum_fin (n : ℕ) (f : ℕ → ℚ) :
    ((List.range n).map f).sum = ∑ i : Fin n, f i.val := by
  rw [← List.sum_toFinset _ (List.nodup_range), List.toFinset_range,
    ← Fin.sum_univ_eq_sum_range]

private theorem applyOperator_getD (c : RationalFeedbackCode) (k : Fin c.2.2.2.length)
    (v : List ℚ) (i : Fin c.1) :
    (applyOperator c k.val v).getD i.val 0 =
      (c.operator k).mulVec (fun j => v.getD j.val 0) i := by
  unfold applyOperator
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range i.isLt]
  simp only [Option.map_some, Option.getD_some, sum_range_eq_sum_fin, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  unfold matrixEntry operator
  have hk : c.2.2.2.getD k.val [] = c.2.2.2.get k := by
    simp only [List.getD_eq_getElem?_getD, getElem?_pos c.2.2.2 k.val k.isLt,
      Option.getD_some, List.get_eq_getElem]
  rw [hk]

theorem wordOutput_eq (c : RationalFeedbackCode) (w : List (Fin c.2.2.2.length)) :
    c.wordOutput (w.map Fin.val) =
      c.representation.output (c.representation.wordAction w c.representation.initial) := by
  have h (i : Fin c.1) :
      ((w.map Fin.val).foldr (applyOperator c) c.2.1).getD i.val 0 =
        c.representation.wordAction w c.representation.initial i := by
    induction w generalizing i with
    | nil => rfl
    | cons k w ih =>
      simp only [List.map_cons, List.foldr_cons, LinearRepresentation.wordAction_cons]
      exact (applyOperator_getD c k _ i).trans (congrArg ((c.operator k).mulVec · i) (funext ih))
  unfold wordOutput
  rw [sum_range_eq_sum_fin]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (c.output i * ·) (h i)

end ContinuousBilinear.RationalFeedbackCode
