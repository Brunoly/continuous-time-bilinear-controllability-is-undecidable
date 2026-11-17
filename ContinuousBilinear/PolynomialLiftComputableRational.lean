import ContinuousBilinear.PolynomialLiftComputableFull
import ContinuousBilinear.CompilerFeedbackCodeProof

namespace ContinuousBilinear
namespace PolynomialLift

open PlantCode

private def tableEntry (g : List (List ℤ)) (i j : ℕ) : ℚ :=
  ((g.getD i []).getD j 0 : ℚ)

def FullPolynomialLiftCode.toRationalFeedback (c : FullPolynomialLiftCode) : RationalFeedbackCode :=
  (c.1, c.2.2.1.map (fun a : ℤ => (a : ℚ)),
    c.2.2.2.1.map (fun a : ℤ => (a : ℚ) / (c.2.2.2.2 : ℚ)),
    c.2.1.map (fun g => tabulateMatrix c.1 (tableEntry g)))

def compileRationalLift (p : IntegerPolynomialCode) : RationalFeedbackCode :=
  (compilePolynomialLift p).toRationalFeedback

private theorem computable_tableEntry :
    Computable (fun q : List (List ℤ) × ℕ × ℕ => tableEntry q.1 q.2.1 q.2.2) := by
  exact primrec_rat_intCast.to_comp.comp ((Primrec.list_getD 0).to_comp.comp
    ((Primrec.list_getD []).to_comp.comp Computable.fst (Computable.fst.comp Computable.snd))
    (Computable.snd.comp Computable.snd))

private theorem computable_feedbackInitial :
    Computable (fun c : FullPolynomialLiftCode => c.2.2.1.map (fun a : ℤ => (a : ℚ))) := by
  have hinput : Computable (fun c : FullPolynomialLiftCode => c.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hcast : Computable₂ (fun (_ : FullPolynomialLiftCode) (a : ℤ) => (a : ℚ)) :=
    (primrec_rat_intCast.to_comp.comp Computable.snd).to₂
  exact computable_list_map hinput hcast

private theorem computable_feedbackOutput :
    Computable (fun c : FullPolynomialLiftCode =>
      c.2.2.2.1.map (fun a : ℤ => (a : ℚ) / (c.2.2.2.2 : ℚ))) := by
  have hnum : Computable (fun c : FullPolynomialLiftCode => c.2.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hden : Computable (fun c : FullPolynomialLiftCode => c.2.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd))
  have hcastNum : Computable (fun q : FullPolynomialLiftCode × ℤ => (q.2 : ℚ)) :=
    primrec_rat_intCast.to_comp.comp Computable.snd
  have hcastDen : Computable (fun q : FullPolynomialLiftCode × ℤ => (q.1.2.2.2.2 : ℚ)) :=
    primrec_rat_intCast.to_comp.comp (hden.comp Computable.fst)
  have hdiv : Computable₂ (fun (c : FullPolynomialLiftCode) (a : ℤ) =>
      (a : ℚ) / (c.2.2.2.2 : ℚ)) :=
    (computable_rat_div.comp hcastNum hcastDen).to₂
  exact computable_list_map hnum hdiv

private theorem computable_feedbackOperatorTable :
    Computable (fun q : ℕ × List (List ℤ) => tabulateMatrix q.1 (tableEntry q.2)) := by
  have project : Computable (fun q : (ℕ × List (List ℤ)) × ℕ × ℕ => (q.1.2, q.2)) :=
    (Computable.snd.comp Computable.fst).pair Computable.snd
  exact computable_tabulateMatrix Computable.fst (computable_tableEntry.comp project)

private theorem computable_feedbackOperators :
    Computable (fun c : FullPolynomialLiftCode =>
      c.2.1.map (fun g => tabulateMatrix c.1 (tableEntry g))) := by
  have hgen : Computable (fun c : FullPolynomialLiftCode => c.2.1) :=
    Computable.fst.comp Computable.snd
  have hproject : Computable (fun q : FullPolynomialLiftCode × List (List ℤ) => (q.1.1, q.2)) :=
    (Computable.fst.comp Computable.fst).pair Computable.snd
  have hgenTable : Computable₂ (fun (c : FullPolynomialLiftCode) (g : List (List ℤ)) =>
      tabulateMatrix c.1 (tableEntry g)) :=
    (computable_feedbackOperatorTable.comp hproject).to₂
  exact computable_list_map hgen hgenTable

theorem computable_toRationalFeedback : Computable FullPolynomialLiftCode.toRationalFeedback := by
  unfold FullPolynomialLiftCode.toRationalFeedback
  exact Computable.fst.pair (computable_feedbackInitial.pair
    (computable_feedbackOutput.pair computable_feedbackOperators))

theorem computable_compileRationalLift : Computable compileRationalLift :=
  computable_toRationalFeedback.comp primrec_compilePolynomialLift.to_comp

theorem compileRationalLift_channelCount (p : IntegerPolynomialCode) :
    (compileRationalLift p).2.2.2.length = p.arity + 2 := by
  simp [compileRationalLift, FullPolynomialLiftCode.toRationalFeedback, compilePolynomialLift]

def compiledRationalChannelEquiv (p : IntegerPolynomialCode) :
    Fin (compileRationalLift p).2.2.2.length ≃ SignChannel p :=
  (finCongr (compileRationalLift_channelCount p)).trans (oscillatorChannelAt (p.arity + 1))

theorem compileRationalLift_initial (p : IntegerPolynomialCode)
    (i : Fin (compileRationalLift p).1) :
    (compileRationalLift p).initial i = (compiledSignInitial p i : ℚ) := by
  unfold RationalFeedbackCode.initial compiledSignInitial
  simp only [compileRationalLift, FullPolynomialLiftCode.toRationalFeedback,
    List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ((compilePolynomialLift p).2.2.1[i.val]?) <;> simp

theorem compileRationalLift_output (p : IntegerPolynomialCode)
    (i : Fin (compileRationalLift p).1) :
    (compileRationalLift p).output i = compiledSignOutput p i := by
  unfold RationalFeedbackCode.output compiledSignOutput
  simp only [compileRationalLift, FullPolynomialLiftCode.toRationalFeedback,
    List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ((compilePolynomialLift p).2.2.2.1[i.val]?) <;> simp

private theorem tabulateMatrix_entry (d : ℕ) (f : ℕ → ℕ → ℚ) (i j : Fin d) :
    (tabulateMatrix d f).getD (i.val * d + j.val) 0 = f i.val j.val := by
  have hd : 0 < d := Nat.zero_lt_of_lt i.isLt
  have hi : i.val * d + j.val < d * d := by
    calc
      i.val * d + j.val < i.val * d + d := Nat.add_lt_add_left j.isLt _
      _ = (i.val + 1) * d := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ d * d := Nat.mul_le_mul_right d (Nat.succ_le_of_lt i.isLt)
  rw [tabulateMatrix, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  simp only [Option.map_some, Option.getD_some, Nat.mul_add_mod_of_lt j.isLt]
  have hdiv : (i.val * d + j.val) / d = i.val := by
    rw [Nat.mul_comm i.val d, Nat.mul_add_div hd, Nat.div_eq_of_lt j.isLt, Nat.add_zero]
  rw [hdiv]

theorem compileRationalLift_operator (p : IntegerPolynomialCode)
    (k : Fin (compileRationalLift p).2.2.2.length) (i j : Fin (compileRationalLift p).1) :
    (compileRationalLift p).operator k i j =
      (compiledSignMatrices p (finCongr (compileRationalLift_channelCount p) k) i j : ℚ) := by
  change Fin (compilePolynomialLift p).1 at i j
  let g := (compilePolynomialLift p).2.1
  have hkG : k.val < g.length := by
    have hlen : (compileRationalLift p).2.2.2.length = g.length := by
      change (g.map (fun g' => tabulateMatrix (compilePolynomialLift p).1 (tableEntry g'))).length = _
      exact List.length_map _
    exact hlen ▸ k.isLt
  have hmap : (compileRationalLift p).2.2.2.get k =
      tabulateMatrix (compilePolynomialLift p).1 (tableEntry (g.getD k.val [])) := by
    change ((g.map (fun g' => tabulateMatrix (compilePolynomialLift p).1 (tableEntry g'))).get
      ⟨k.val, k.isLt⟩) = _
    rw [List.get_eq_getElem, List.getElem_map]
    simp only [List.getD_eq_getElem?_getD, getElem?_pos g k.val hkG, Option.getD_some]
  change ((compileRationalLift p).2.2.2.get k).getD
    (i.val * (compilePolynomialLift p).1 + j.val) 0 = tableEntry (g.getD k.val []) i.val j.val
  rw [hmap, tabulateMatrix_entry]

end PolynomialLift
end ContinuousBilinear
