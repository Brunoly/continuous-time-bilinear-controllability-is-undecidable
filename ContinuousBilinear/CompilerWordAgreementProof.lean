import ContinuousBilinear.CompilerWordCoefficientProof
import ContinuousBilinear.CompilerWordEnumerationProof

namespace ContinuousBilinear.RationalFeedbackCode

open PolynomialLift

/-- Equality of word coefficients on the finite cutoff for two codes with the same alphabet. -/
def wordOutputsAgree (p : RationalFeedbackCode × RationalFeedbackCode) : Prop :=
  p.1.2.2.2.length = p.2.2.2.2.length ∧
    ∀ w ∈ wordsUpTo (List.range p.1.2.2.2.length) (p.1.1 + p.2.1),
      p.1.wordOutput w = p.2.wordOutput w

theorem computable_wordOutputsAgree : ComputablePred wordOutputsAgree := by
  let P := RationalFeedbackCode × RationalFeedbackCode
  let hlen : Computable (fun p : P => p.1.2.2.2.length) :=
    Computable.list_length.comp
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
  let hlen' : Computable (fun p : P => p.2.2.2.2.length) :=
    Computable.list_length.comp
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))
  let hy := computablePred_eq hlen hlen'
  let hn : Computable (fun p : P => p.1.1 + p.2.1) :=
    Primrec.nat_add.to_comp.comp (Computable.fst.comp Computable.fst)
      (Computable.fst.comp Computable.snd)
  let hw := computable_wordsUpTo.comp (Primrec.list_range.to_comp.comp hlen) hn
  let Q := P × List ℕ × Bool
  have hleft := computable_wordOutput.comp
    (Computable.fst.comp Computable.fst : Computable (fun p : Q => p.1.1))
    (Computable.fst.comp Computable.snd : Computable (fun p : Q => p.2.1))
  have hright := computable_wordOutput.comp
    (Computable.snd.comp Computable.fst : Computable (fun p : Q => p.1.2))
    (Computable.fst.comp Computable.snd : Computable (fun p : Q => p.2.1))
  have he := computablePred_eq hleft hright
  have hb : Computable (fun p : Q => decide (p.1.1.wordOutput p.2.1 = p.1.2.wordOutput p.2.1)) :=
    he.decide.of_eq (g := fun p : Q => decide (p.1.1.wordOutput p.2.1 = p.1.2.wordOutput p.2.1))
      (fun _ => rfl)
  have hstep : Computable₂ (fun (p : P) (q : List ℕ × Bool) =>
      decide (p.1.wordOutput q.1 = p.2.wordOutput q.1) && q.2) :=
    (Primrec.and.to_comp.comp hb (Computable.snd.comp Computable.snd)).to₂
  have hfold := computable_list_foldr [] hw (Computable.const true) hstep
  let check (p : P) : Bool := decide (p.1.2.2.2.length = p.2.2.2.2.length) &&
      (wordsUpTo (List.range p.1.2.2.2.length) (p.1.1 + p.2.1)).foldr
        (fun w s => decide (p.1.wordOutput w = p.2.wordOutput w) && s) true
  have hc : Computable check := Primrec.and.to_comp.comp hy.decide hfold
  have hcheck : wordOutputsAgree = (fun p : P => (check p : Prop)) := by
    funext p
    apply propext
    simp only [wordOutputsAgree, check, Bool.and_eq_true, decide_eq_true_eq]
    apply and_congr_right
    intro _
    generalize wordsUpTo (List.range p.1.2.2.2.length) (p.1.1 + p.2.1) = ws
    induction ws with
    | nil => simp
    | cons w ws ih => simp [ih]
  exact ComputablePred.computable_iff.mpr ⟨check, hc, hcheck⟩

/-- The rational realization interpreted over the alphabet of another code with the same size. -/
def representationWithAlphabet (c : RationalFeedbackCode) {m : ℕ}
    (hm : m = c.2.2.2.length) : LinearRepresentation ℚ (Fin c.1 → ℚ) (Fin m) :=
  { c.representation with operator := fun k => c.representation.operator (Fin.cast hm k) }

private theorem representationWithAlphabet_word (c : RationalFeedbackCode) {m : ℕ}
    (hm : m = c.2.2.2.length) (w : List (Fin m)) :
    (c.representationWithAlphabet hm).wordAction w =
      c.representation.wordAction (w.map (Fin.cast hm)) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    rw [LinearRepresentation.wordAction, List.map_cons, LinearRepresentation.wordAction, ih]
    rfl

theorem exponentialCoefficient_eq_of_wordOutputsAgree (c e : RationalFeedbackCode)
    (h : wordOutputsAgree (c, e)) (u : Fin c.2.2.2.length → ℝ) :
    c.representation.exponentialCoefficient (Pi.basisFun ℚ (Fin c.1)) u =
      (e.representationWithAlphabet h.1).exponentialCoefficient
        (Pi.basisFun ℚ (Fin e.1)) u := by
  apply LinearRepresentation.exponentialCoefficient_eq_of_words
  apply LinearRepresentation.all_wordOutput_eq_of_bounded
  intro w hw
  have hlength : w.length ≤ c.1 + e.1 := by
    simpa only [Module.finrank_fin_fun] using hw
  have hmem : w.map Fin.val ∈ wordsUpTo (List.range c.2.2.2.length) (c.1 + e.1) := by
    apply (mem_wordsUpTo _ _ _).mpr
    refine ⟨by simpa only [List.length_map] using hlength, ?_⟩
    intro a ha
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp ha
    exact List.mem_range.mpr k.isLt
  have he := h.2 (w.map Fin.val) hmem
  rw [wordOutput_eq] at he
  have hh := e.wordOutput_eq (w.map (Fin.cast h.1))
  rw [List.map_map] at hh
  change e.wordOutput (w.map Fin.val) = _ at hh
  rw [hh] at he
  exact he.trans (by rw [representationWithAlphabet_word]; rfl)

end ContinuousBilinear.RationalFeedbackCode
