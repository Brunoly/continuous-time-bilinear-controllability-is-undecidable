import ContinuousBilinear.CompilerWordCoefficientProof
import ContinuousBilinear.CompilerWordEnumerationProof
import ContinuousBilinear.CompilerPlantTabulationProof

namespace ContinuousBilinear.RationalFeedbackCode

open PlantCode PolynomialLift

/-- The finite list of words over the encoded control alphabet up to length `k`. -/
def boundedWords (c : RationalFeedbackCode) (k : ℕ) : List (List ℕ) :=
  wordsUpTo (List.range c.2.2.2.length) k

theorem computable_boundedWords : Computable₂ boundedWords := by
  have hchannels : Computable (fun p : RationalFeedbackCode × ℕ => p.1.2.2.2.length) :=
    Computable.list_length.comp
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
  exact (computable_wordsUpTo.comp
    (Primrec.list_range.to_comp.comp hchannels) Computable.snd).to₂

private theorem mem_boundedWords (c : RationalFeedbackCode) (k : ℕ) (w : List ℕ) :
    w ∈ c.boundedWords k ↔ w.length ≤ k ∧ ∀ a ∈ w, a < c.2.2.2.length := by
  simp only [boundedWords, mem_wordsUpTo, List.mem_range]

/-- Decode a bounded word using the actual finite control alphabet. -/
def boundedWordAt (c : RationalFeedbackCode) (k : ℕ) (i : Fin (c.boundedWords k).length) :
    List (Fin c.2.2.2.length) :=
  let w := (c.boundedWords k).get i
  w.pmap (fun a ha => ⟨a, ha⟩)
    ((mem_boundedWords c k w).mp (List.get_mem _ i)).2

@[simp] theorem boundedWordAt_map_val (c : RationalFeedbackCode) (k : ℕ)
    (i : Fin (c.boundedWords k).length) :
    (c.boundedWordAt k i).map Fin.val = (c.boundedWords k).get i := by
  unfold boundedWordAt
  rw [List.pmap_eq_map_attach, List.map_map]
  exact List.attach_map_subtype_val _

theorem boundedWordAt_length_le (c : RationalFeedbackCode) (k : ℕ)
    (i : Fin (c.boundedWords k).length) : (c.boundedWordAt k i).length ≤ k := by
  have h := ((mem_boundedWords c k _).mp (List.get_mem (c.boundedWords k) i)).1
  rwa [← boundedWordAt_map_val, List.length_map] at h

theorem exists_boundedWordAt_eq (c : RationalFeedbackCode) (k : ℕ)
    (w : List (Fin c.2.2.2.length)) (hw : w.length ≤ k) :
    ∃ i : Fin (c.boundedWords k).length, c.boundedWordAt k i = w := by
  have hm : w.map Fin.val ∈ c.boundedWords k := by
    apply (mem_boundedWords c k _).mpr
    refine ⟨by simpa using hw, ?_⟩
    intro a ha
    obtain ⟨a', _, rfl⟩ := List.mem_map.mp ha
    exact a'.isLt
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hm
  refine ⟨⟨i, hi⟩, ?_⟩
  have hmap : (c.boundedWordAt k ⟨i, hi⟩).map Fin.val = w.map Fin.val := by
    rw [boundedWordAt_map_val]
    exact hget
  exact (List.map_injective_iff.mpr Fin.val_injective) hmap

private theorem boundedWords_getD (c : RationalFeedbackCode) (k : ℕ)
    (i : Fin (c.boundedWords k).length) :
    (c.boundedWords k).getD i.val [] = (c.boundedWordAt k i).map Fin.val := by
  simp only [boundedWordAt_map_val, List.getD_eq_getElem?_getD,
    getElem?_pos (c.boundedWords k) i.val i.isLt, Option.getD_some, List.get_eq_getElem]

/-- Output of the word at the given bounded-word index. -/
def wordMomentEntry (c : RationalFeedbackCode) (k i : ℕ) : ℚ :=
  c.wordOutput ((c.boundedWords k).getD i [])

/-- Output of the prefix, the inserted word, and the suffix in that order. -/
def wordHankelEntry (c : RationalFeedbackCode) (k : ℕ) (middle : List ℕ) (i j : ℕ) : ℚ :=
  let ws := c.boundedWords k
  c.wordOutput (ws.getD i [] ++ middle ++ ws.getD j [])

/-- The word outputs in bounded-word enumeration order. -/
def wordMoments (c : RationalFeedbackCode) (k : ℕ) : List ℚ :=
  (c.boundedWords k).map c.wordOutput

/-- The finite square Hankel table, in row-major order, optionally with an inserted word.
Use the empty inserted word for the ordinary Hankel table and a singleton for a generator shift. -/
def wordHankel (c : RationalFeedbackCode) (k : ℕ) (middle : List ℕ) : List ℚ :=
  tabulateMatrix (c.boundedWords k).length (c.wordHankelEntry k middle)

private theorem computable_boundedWords_getD :
    Computable (fun p : (RationalFeedbackCode × ℕ) × ℕ =>
      (p.1.1.boundedWords p.1.2).getD p.2 []) := by
  exact (Primrec.list_getD []).to_comp.comp
    ((computable_boundedWords.comp Computable.fst Computable.snd).comp Computable.fst)
    Computable.snd

theorem computable_wordMomentEntry :
    Computable (fun p : (RationalFeedbackCode × ℕ) × ℕ =>
      p.1.1.wordMomentEntry p.1.2 p.2) :=
  computable_wordOutput.comp (Computable.fst.comp Computable.fst) computable_boundedWords_getD

theorem computable_wordHankelEntry :
    Computable (fun p : (RationalFeedbackCode × ℕ × List ℕ) × ℕ × ℕ =>
      p.1.1.wordHankelEntry p.1.2.1 p.1.2.2 p.2.1 p.2.2) := by
  let P := (RationalFeedbackCode × ℕ × List ℕ) × ℕ × ℕ
  have hc : Computable (fun p : P => p.1.1) := Computable.fst.comp Computable.fst
  have hk : Computable (fun p : P => p.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hmid : Computable (fun p : P => p.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hi : Computable (fun p : P => p.2.1) := Computable.fst.comp Computable.snd
  have hj : Computable (fun p : P => p.2.2) := Computable.snd.comp Computable.snd
  have hl := computable_boundedWords_getD.comp ((hc.pair hk).pair hi)
  have hr := computable_boundedWords_getD.comp ((hc.pair hk).pair hj)
  exact computable_wordOutput.comp hc (Primrec.list_append.to_comp.comp
    (Primrec.list_append.to_comp.comp hl hmid) hr)

theorem computable_wordMoments : Computable₂ wordMoments := by
  have hw : Computable (fun p : RationalFeedbackCode × ℕ => p.1.boundedWords p.2) :=
    computable_boundedWords.comp Computable.fst Computable.snd
  have hf : Computable₂ (fun p : RationalFeedbackCode × ℕ => p.1.wordOutput) :=
    (computable_wordOutput.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂
  exact (computable_list_map hw hf).to₂

private theorem computable_boundedWords_length :
    Computable₂ (fun (c : RationalFeedbackCode) k => (c.boundedWords k).length) :=
  (Computable.list_length.comp (computable_boundedWords.comp Computable.fst Computable.snd)).to₂

theorem computable_wordHankel :
    Computable (fun p : RationalFeedbackCode × ℕ × List ℕ => p.1.wordHankel p.2.1 p.2.2) := by
  let P := RationalFeedbackCode × ℕ × List ℕ
  let n (p : P) := (p.1.boundedWords p.2.1).length
  have hn : Computable n :=
    computable_boundedWords_length.comp Computable.fst (Computable.fst.comp Computable.snd)
  have hnp : Computable (fun a : P × ℕ => n a.1) := hn.comp Computable.fst
  have hdiv : Computable (fun a : P × ℕ => a.2 / n a.1) :=
    Primrec.nat_div.to_comp.comp Computable.snd hnp
  have hmod : Computable (fun a : P × ℕ => a.2 % n a.1) :=
    Primrec.nat_mod.to_comp.comp Computable.snd hnp
  have hcoords : Computable (fun a : P × ℕ => (a.1, a.2 / n a.1, a.2 % n a.1)) :=
    Computable.fst.pair (hdiv.pair hmod)
  have hentries : Computable₂ (fun (p : P) (a : ℕ) =>
      p.1.wordHankelEntry p.2.1 p.2.2 (a / n p) (a % n p)) :=
    (computable_wordHankelEntry.comp hcoords).to₂
  have hindices : Computable (fun a : P => List.range (n a * n a)) :=
    Primrec.list_range.to_comp.comp (Primrec.nat_mul.to_comp.comp hn hn)
  exact computable_list_map hindices hentries

theorem wordMomentEntry_eq (c : RationalFeedbackCode) (k : ℕ)
    (i : Fin (c.boundedWords k).length) :
    c.wordMomentEntry k i.val =
      c.representation.output (c.representation.wordAction (c.boundedWordAt k i)
        c.representation.initial) := by
  rw [wordMomentEntry, boundedWords_getD, wordOutput_eq]

theorem wordHankelEntry_eq (c : RationalFeedbackCode) (k : ℕ) (middle : List (Fin c.2.2.2.length))
    (i j : Fin (c.boundedWords k).length) :
    c.wordHankelEntry k (middle.map Fin.val) i.val j.val =
      c.representation.output (c.representation.wordAction (c.boundedWordAt k i)
        (c.representation.wordAction middle
          (c.representation.wordAction (c.boundedWordAt k j) c.representation.initial))) := by
  simp only [wordHankelEntry, boundedWords_getD, ← List.map_append, wordOutput_eq,
    LinearRepresentation.wordAction_append]

theorem wordMoments_getD (c : RationalFeedbackCode) (k : ℕ) (i : Fin (c.boundedWords k).length) :
    (c.wordMoments k).getD i.val 0 = c.wordMomentEntry k i.val := by
  simp only [wordMoments, wordMomentEntry, List.getD_eq_getElem?_getD, List.getElem?_map,
    getElem?_pos (c.boundedWords k) i.val i.isLt, Option.map_some, Option.getD_some]

theorem wordHankel_getD (c : RationalFeedbackCode) (k : ℕ) (middle : List ℕ)
    (i j : Fin (c.boundedWords k).length) :
    (c.wordHankel k middle).getD (i.val * (c.boundedWords k).length + j.val) 0 =
      c.wordHankelEntry k middle i.val j.val := by
  let n := (c.boundedWords k).length
  let M : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j =>
    c.wordHankelEntry k middle i.val j.val
  have h : c.wordHankel k middle = matrixEntries M :=
    tabulateMatrix_eq_matrixEntries _ _ (fun _ _ => rfl)
  rw [h]
  exact matrixEntries_getD M i j 0

end ContinuousBilinear.RationalFeedbackCode
