import ContinuousBilinear.CompilerFeedbackNormalizationProof
import ContinuousBilinear.CompilerIntegerNormalizationCodeProof
import ContinuousBilinear.CompilerMatrixOperationsProof

namespace ContinuousBilinear

/-- Dimension, initial vector, output row, and row-major control matrices of a
rational representation. -/
abbrev RationalFeedbackCode := ℕ × List ℚ × List ℚ × List (List ℚ)

namespace RationalFeedbackCode

open FeedbackCoordinates PlantCode

def initial (c : RationalFeedbackCode) (i : Fin c.1) : ℚ := c.2.1.getD i.val 0

def output (c : RationalFeedbackCode) (i : Fin c.1) : ℚ := c.2.2.1.getD i.val 0

def operator (c : RationalFeedbackCode) (k : Fin c.2.2.2.length) :
    Matrix (Fin c.1) (Fin c.1) ℚ :=
  fun i j => (c.2.2.2.get k).getD (i.val * c.1 + j.val) 0

private def diagonalEntry (i j : ℕ) : ℚ := if i = j then 1 else 0

private def initialEntry (c : RationalFeedbackCode) (i : ℕ) : ℚ :=
  c.2.1.getD (i - 1) 0

private def outputEntry (c : RationalFeedbackCode) (j : ℕ) : ℚ :=
  c.2.2.1.getD (j - 1) 0

private def basisEntry (c : RationalFeedbackCode) (i j : ℕ) : ℚ :=
  if i = 0 then
    if j = 0 then 1 else -outputEntry c j
  else
    if j = 0 then initialEntry c i else diagonalEntry i j

private def inverseEntry (c : RationalFeedbackCode) (i j : ℕ) : ℚ :=
  if i = 0 then
    if j = 0 then 1 / 2 else (1 / 2) * outputEntry c j
  else
    if j = 0 then -(initialEntry c i * (1 / 2))
    else diagonalEntry i j - (initialEntry c i * (1 / 2)) * outputEntry c j

private def controlEntry (c : RationalFeedbackCode) (k i j : ℕ) : ℚ :=
  if i = 0 then 0 else
    if j = 0 then 0 else
      if k = 0 then diagonalEntry i j
      else (c.2.2.2.getD (k - 1) []).getD ((i - 1) * c.1 + (j - 1)) 0

@[irreducible] private def normalizedControlEntry (c : RationalFeedbackCode) (k i j : ℕ) : ℚ :=
  productEntries (c.1 + 1)
    (productEntries (c.1 + 1) (inverseEntry c) (controlEntry c k)) (basisEntry c) i j

/-- The feedback plant in rational coordinates with canonical rank-one drift. -/
def normalizedCode (c : RationalFeedbackCode) : RationalPlantCode :=
  tabulatePlant (c.1 + 1) (c.2.2.2.length + 1)
    (fun i j => if i = j ∧ i = 0 then 1 else 0) (normalizedControlEntry c)

/-- Canonical integer encoding after changing coordinates and clearing control denominators. -/
def integerCode (c : RationalFeedbackCode) : IntegerPlantCode :=
  clearControlCode c.normalizedCode

private theorem computable_getD {α β : Type*} [Primcodable α] [Primcodable β]
    {xs : α → List β} {i : α → ℕ} (hxs : Computable xs)
    (hi : Computable i) (fallback : β) : Computable fun a => (xs a).getD (i a) fallback :=
  (Primrec.option_getD.to_comp.comp (Primrec.list_getElem?.to_comp.comp hxs hi)
    (Computable.const fallback)).of_eq fun _ => rfl

private theorem computable_pred {α : Type*} [Primcodable α] {i : α → ℕ}
    (hi : Computable i) : Computable fun a => i a - 1 :=
  Primrec.nat_sub.to_comp.comp hi (Computable.const 1)

private theorem computable_diagonalEntry {α : Type*} [Primcodable α] {i j : α → ℕ}
    (hi : Computable i) (hj : Computable j) : Computable fun a => diagonalEntry (i a) (j a) :=
  computable_cond_of_computablePred (computablePred_eq hi hj) (Computable.const 1)
    (Computable.const 0)

private theorem computable_initialEntry {α : Type*} [Primcodable α]
    {c : α → RationalFeedbackCode} {i : α → ℕ} (hc : Computable c) (hi : Computable i) :
    Computable fun a => initialEntry (c a) (i a) :=
  computable_getD (Computable.fst.comp (Computable.snd.comp hc)) (computable_pred hi) 0

private theorem computable_outputEntry {α : Type*} [Primcodable α]
    {c : α → RationalFeedbackCode} {j : α → ℕ} (hc : Computable c) (hj : Computable j) :
    Computable fun a => outputEntry (c a) (j a) :=
  computable_getD (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hc)))
    (computable_pred hj) 0

private theorem computable_basisEntry : Computable fun p : RationalFeedbackCode × ℕ × ℕ =>
    basisEntry p.1 p.2.1 p.2.2 := by
  let hi : Computable (fun p : RationalFeedbackCode × ℕ × ℕ => p.2.1) :=
    Computable.fst.comp Computable.snd
  let hj : Computable (fun p : RationalFeedbackCode × ℕ × ℕ => p.2.2) :=
    Computable.snd.comp Computable.snd
  exact computable_cond_of_computablePred (computablePred_eq hi (Computable.const 0))
    (computable_cond_of_computablePred (computablePred_eq hj (Computable.const 0))
      (Computable.const 1) (computable_rat_neg.comp (computable_outputEntry Computable.fst hj)))
    (computable_cond_of_computablePred (computablePred_eq hj (Computable.const 0))
      (computable_initialEntry Computable.fst hi) (computable_diagonalEntry hi hj))

private theorem computable_inverseEntry : Computable fun p : RationalFeedbackCode × ℕ × ℕ =>
    inverseEntry p.1 p.2.1 p.2.2 := by
  let hi : Computable (fun p : RationalFeedbackCode × ℕ × ℕ => p.2.1) :=
    Computable.fst.comp Computable.snd
  let hj : Computable (fun p : RationalFeedbackCode × ℕ × ℕ => p.2.2) :=
    Computable.snd.comp Computable.snd
  let hhalf : Computable (fun _ : RationalFeedbackCode × ℕ × ℕ => (1 / 2 : ℚ)) :=
    Computable.const _
  let htail := computable_rat_mul.comp (computable_initialEntry Computable.fst hi) hhalf
  exact computable_cond_of_computablePred (computablePred_eq hi (Computable.const 0))
    (computable_cond_of_computablePred (computablePred_eq hj (Computable.const 0))
      hhalf (computable_rat_mul.comp hhalf (computable_outputEntry Computable.fst hj)))
    (computable_cond_of_computablePred (computablePred_eq hj (Computable.const 0))
      (computable_rat_neg.comp htail) (computable_rat_sub.comp (computable_diagonalEntry hi hj)
        (computable_rat_mul.comp htail (computable_outputEntry Computable.fst hj))))

private theorem computable_controlEntry :
    Computable fun p : (RationalFeedbackCode × ℕ) × ℕ × ℕ =>
      controlEntry p.1.1 p.1.2 p.2.1 p.2.2 := by
  let hc : Computable (fun p : (RationalFeedbackCode × ℕ) × ℕ × ℕ => p.1.1) :=
    Computable.fst.comp Computable.fst
  let hk : Computable (fun p : (RationalFeedbackCode × ℕ) × ℕ × ℕ => p.1.2) :=
    Computable.snd.comp Computable.fst
  let hi : Computable (fun p : (RationalFeedbackCode × ℕ) × ℕ × ℕ => p.2.1) :=
    Computable.fst.comp Computable.snd
  let hj : Computable (fun p : (RationalFeedbackCode × ℕ) × ℕ × ℕ => p.2.2) :=
    Computable.snd.comp Computable.snd
  let hmat := computable_getD
    (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hc)))
    (computable_pred hk) []
  let hentry := computable_getD hmat
    (Primrec.nat_add.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (computable_pred hi) (Computable.fst.comp hc))
      (computable_pred hj)) 0
  exact computable_cond_of_computablePred (computablePred_eq hi (Computable.const 0))
    (Computable.const 0)
    (computable_cond_of_computablePred (computablePred_eq hj (Computable.const 0))
      (Computable.const 0)
      (computable_cond_of_computablePred (computablePred_eq hk (Computable.const 0))
        (computable_diagonalEntry hi hj) hentry))

private theorem computable_conjugationEntries {α : Type*} [Primcodable α]
    {n : α → ℕ} {a b d : α × ℕ × ℕ → ℚ}
    (hn : Computable n) (ha : Computable a) (hb : Computable b) (hd : Computable d) :
    Computable (fun p : α × ℕ × ℕ =>
      productEntries (n p.1)
        (productEntries (n p.1) (fun i j => a (p.1, i, j)) (fun i j => b (p.1, i, j)))
        (fun i j => d (p.1, i, j)) p.2.1 p.2.2) := by
  let g := fun p : α × ℕ × ℕ =>
    productEntries (n p.1) (fun i j => a (p.1, i, j)) (fun i j => b (p.1, i, j)) p.2.1 p.2.2
  have hg : Computable g := computable_productEntries (n := n) (a := a) (b := b) hn ha hb
  have hp := computable_productEntries (n := n) (a := g) (b := d) hn hg hd
  exact hp.of_eq fun p => by rcases p with ⟨x, i, j⟩; rfl

private theorem computable_normalizedControlEntry :
    Computable fun p : (RationalFeedbackCode × ℕ) × ℕ × ℕ =>
      normalizedControlEntry p.1.1 p.1.2 p.2.1 p.2.2 := by
  let n := fun p : RationalFeedbackCode × ℕ => p.1.1 + 1
  let a := fun p : (RationalFeedbackCode × ℕ) × ℕ × ℕ => inverseEntry p.1.1 p.2.1 p.2.2
  let b := fun p : (RationalFeedbackCode × ℕ) × ℕ × ℕ => controlEntry p.1.1 p.1.2 p.2.1 p.2.2
  let d := fun p : (RationalFeedbackCode × ℕ) × ℕ × ℕ => basisEntry p.1.1 p.2.1 p.2.2
  have hn : Computable n := Primrec.succ.to_comp.comp (Computable.fst.comp Computable.fst)
  have hargs : Computable (fun p : (RationalFeedbackCode × ℕ) × ℕ × ℕ => (p.1.1, p.2)) :=
    (Computable.fst.comp Computable.fst).pair Computable.snd
  have ha0 := computable_inverseEntry.comp hargs
  have ha : Computable a := ha0.of_eq (g := a) (fun _ => rfl)
  have hb : Computable b := computable_controlEntry
  have hd0 := computable_basisEntry.comp hargs
  have hd : Computable d := hd0.of_eq (g := d) (fun _ => rfl)
  have hp := computable_conjugationEntries (n := n) (a := a) (b := b) (d := d) hn ha hb hd
  refine hp.of_eq (g := fun p : (RationalFeedbackCode × ℕ) × ℕ × ℕ =>
    normalizedControlEntry p.1.1 p.1.2 p.2.1 p.2.2) ?_
  intro p
  unfold normalizedControlEntry
  rfl

theorem computable_normalizedCode : Computable normalizedCode := by
  have hn : Computable (fun c : RationalFeedbackCode => c.1 + 1) :=
    Primrec.succ.to_comp.comp Computable.fst
  have hm : Computable (fun c : RationalFeedbackCode => c.2.2.2.length + 1) :=
    Primrec.succ.to_comp.comp (Primrec.list_length.to_comp.comp
      (Computable.snd.comp (Computable.snd.comp Computable.snd)))
  have hdrift : Primrec (fun p : RationalFeedbackCode × ℕ × ℕ =>
      if p.2.1 = p.2.2 ∧ p.2.1 = 0 then (1 : ℚ) else 0) :=
    Primrec.ite ((Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).and
        (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0)))
      (Primrec.const (1 : ℚ)) (Primrec.const 0)
  refine (computable_tabulatePlant hn hm hdrift.to_comp computable_normalizedControlEntry).of_eq ?_
  intro p
  rfl

theorem computable_integerCode : Computable integerCode :=
  computable_clearControlCode.comp computable_normalizedCode

private theorem basisEntry_eq (c : RationalFeedbackCode) (i j : Fin (c.1 + 1)) :
    basisEntry c i.val j.val = basisMatrix c.initial c.output i j := by
  refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j <;>
    simp [basisEntry, basisMatrix, diagonalEntry, initialEntry, outputEntry, initial, output,
      Fin.ext_iff]

private theorem inverseEntry_eq (c : RationalFeedbackCode) (i j : Fin (c.1 + 1)) :
    inverseEntry c i.val j.val = inverseMatrix c.initial c.output i j := by
  refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j <;>
    simp [inverseEntry, inverseMatrix, diagonalEntry, initialEntry, outputEntry, initial, output,
      Fin.ext_iff]

private theorem controlEntry_eq (c : RationalFeedbackCode) (k : Fin (c.2.2.2.length + 1))
    (i j : Fin (c.1 + 1)) : controlEntry c k.val i.val j.val =
      rationalControls c.operator k i j := by
  refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
  all_goals
    refine Fin.cases ?_ (fun s => ?_) k <;>
      simp [controlEntry, diagonalEntry, operator, rationalControls, controlBlock,
        Matrix.one_apply, Fin.ext_iff, List.get_eq_getElem, List.getD_eq_getElem?_getD]

private theorem normalizedControlEntry_eq (c : RationalFeedbackCode)
    (k : Fin (c.2.2.2.length + 1)) (i j : Fin (c.1 + 1)) :
    normalizedControlEntry c k.val i.val j.val =
      (normalizedRationalFeedback c.operator c.initial c.output).control k i j :=
  by
    unfold normalizedControlEntry
    exact productEntries_eq_matrix_mul
      (fun a b => productEntries_eq_matrix_mul (inverseEntry_eq c) (controlEntry_eq c k) a b)
      (basisEntry_eq c) i j

private theorem canonicalDrift_entry (d : ℕ) (i j : Fin (d + 1)) :
    (if i.val = j.val ∧ i.val = 0 then (1 : ℚ) else 0) = canonicalDrift d i j := by
  by_cases hij : i = j
  · subst j
    exact (show (if i.val = i.val ∧ i.val = 0 then (1 : ℚ) else 0) =
      (if i.val = 0 then 1 else 0) by simp).trans
      (Matrix.diagonal_apply_eq (fun k : Fin (d + 1) => if k.val = 0 then (1 : ℚ) else 0) i).symm
  · have h' : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have ht : (if i.val = j.val ∧ i.val = 0 then (1 : ℚ) else 0) = 0 := by simp [h']
    exact ht.trans (Matrix.diagonal_apply_ne _ hij).symm

theorem normalizedCode_eq_encode (c : RationalFeedbackCode) :
    normalizedCode c = encode (normalizedRationalFeedback c.operator c.initial c.output) := by
  let P := normalizedRationalFeedback c.operator c.initial c.output
  let drift := fun i j : ℕ => if i = j ∧ i = 0 then (1 : ℚ) else 0
  have hn : P.dimension = c.1 + 1 := rfl
  have hm : P.controls = c.2.2.2.length + 1 := rfl
  change tabulatePlant (c.1 + 1) (c.2.2.2.length + 1) drift (normalizedControlEntry c) =
    encode P
  rw [← hn, ← hm]
  apply tabulatePlant_eq_encode P
  · exact canonicalDrift_entry c.1
  · exact normalizedControlEntry_eq c

theorem integerCode_decode (c : RationalFeedbackCode) :
    c.integerCode.decode =
      (normalizedRationalFeedback c.operator c.initial c.output).clearControlDenominators := by
  unfold integerCode
  rw [normalizedCode_eq_encode, clearControlCode_eq_encode _ (wellFormed_encode _),
    decode_encode, decode_encode]

theorem integerCode_correct (c : RationalFeedbackCode)
    (h : ∑ i, c.output i * c.initial i = 1)
    (hcomm : ∀ i j, Commute (c.operator i) (c.operator j)) :
    CanonicalIntegerInstance c.integerCode ∧
      (IntegerGlobalControllability c.integerCode ↔
        GloballyControllable (realFeedbackData c.operator c.initial c.output).plant) := by
  have hd : 2 ≤ c.1 + 1 := by
    by_contra hn
    have hzero : c.1 = 0 := by omega
    let : IsEmpty (Fin c.1) := hzero ▸ (inferInstance : IsEmpty (Fin 0))
    simp [Finset.univ_eq_empty] at h
  let P := normalizedRationalFeedback c.operator c.initial c.output
  have hcode : c.normalizedCode = encode P := normalizedCode_eq_encode c
  have hwf : c.normalizedCode.WellFormed := hcode.symm ▸ (wellFormed_encode P)
  have hP : c.normalizedCode.decode = P := hcode.symm ▸ (decode_encode P)
  have hdim : 2 ≤ c.normalizedCode.1 := hd
  have hdrift : c.normalizedCode.decode.drift =
      Matrix.diagonal (fun i => if i.val = 0 then 1 else 0) := hP.symm ▸ (rfl : P.drift = _)
  have hC : ∀ i j, Commute (c.normalizedCode.decode.control i)
      (c.normalizedCode.decode.control j) :=
    hP.symm ▸ normalizedRationalFeedback_commute c.operator c.initial c.output h hcomm
  obtain ⟨hc, heq⟩ := clearControlCode_correct c.normalizedCode hwf hdim hdrift hC
  refine ⟨hc, heq.trans ?_⟩
  unfold RationalGlobalControllability
  rw [and_iff_right hwf, hP]
  exact globallyControllable_normalizedRationalFeedback c.operator c.initial c.output h

end RationalFeedbackCode
end ContinuousBilinear
