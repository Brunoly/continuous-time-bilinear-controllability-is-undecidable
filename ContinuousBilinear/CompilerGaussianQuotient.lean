import ContinuousBilinear.CompilerGaussianComputableProof
import ContinuousBilinear.CompilerHankelTables
import ContinuousBilinear.CompilerQuotientCodeCorrectness
import ContinuousBilinear.CompilerSchurFactorization

namespace ContinuousBilinear.RationalFeedbackCode

open PolynomialLift GaussianElimination

def hankelEliminationTable (c : RationalFeedbackCode) : Table :=
  let n := (c.boundedWords c.1).length
  (n, n, c.wordHankel c.1 [])

def selectedWords (c : RationalFeedbackCode) (indices : List ℕ) : List (List ℕ) :=
  indices.map fun i => (c.boundedWords c.1).getD i []

def coordinatesOfSelection (c : RationalFeedbackCode) (s : Selection) : QuotientCoordinateData :=
  (c, c.selectedWords s.1, c.selectedWords s.2.1, s.2.2)

/-- Compute the reachable/observable quotient by rational Gaussian elimination
of the observation table on bounded word states. -/
def gaussianQuotient (c : RationalFeedbackCode) : RationalFeedbackCode :=
  (c.coordinatesOfSelection (eliminate c.hankelEliminationTable)).quotientCode

set_option maxHeartbeats 600000 in
private theorem computable_hankelEliminationTable : Computable hankelEliminationTable := by
  have ha : Computable (fun c : RationalFeedbackCode => (c, c.1, ([] : List ℕ))) :=
    Computable.id.pair (Computable.fst.pair (Computable.const []))
  have hn : Computable (fun c : RationalFeedbackCode => (c.boundedWords c.1).length) :=
    Computable.list_length.comp (computable_boundedWords.comp Computable.id Computable.fst)
  have hvalues : Computable (fun c : RationalFeedbackCode => c.wordHankel c.1 []) :=
    (computable_wordHankel.comp ha).of_eq fun _ => rfl
  exact (hn.pair (hn.pair hvalues)).of_eq (g := hankelEliminationTable) fun _ => rfl

private theorem computable_selectedWords : Computable₂ selectedWords := by
  let P := RationalFeedbackCode × List ℕ
  have hws : Computable (fun p : P => p.1.boundedWords p.1.1) :=
    computable_boundedWords.comp Computable.fst (Computable.fst.comp Computable.fst)
  have hget : Computable₂ (fun (p : P) (i : ℕ) => (p.1.boundedWords p.1.1).getD i []) :=
    (GaussianPivot.computable_getD (hws.comp Computable.fst) Computable.snd []).to₂
  exact (computable_list_map (α := P) Computable.snd hget).to₂

private theorem computable_coordinatesOfSelection : Computable₂ coordinatesOfSelection := by
  let P := RationalFeedbackCode × Selection
  have hc : Computable (fun p : P => p.1) := Computable.fst
  have hr : Computable (fun p : P => p.2.1) := Computable.fst.comp Computable.snd
  have hq : Computable (fun p : P => p.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hi : Computable (fun p : P => p.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  exact (hc.pair ((computable_selectedWords.comp hc hr).pair
    ((computable_selectedWords.comp hc hq).pair hi))).to₂

theorem computable_gaussianQuotient : Computable gaussianQuotient :=
  QuotientCoordinateData.computable_quotientCode.comp (computable_coordinatesOfSelection.comp
    Computable.id (computable_eliminate.comp computable_hankelEliminationTable))

private theorem getD_map_of_lt {α β : Type*} {l : List α} {i : ℕ}
    (hi : i < l.length) (f : α → β) (a : α) (b : β) :
    (l.map f).getD i b = f (l.getD i a) := by
  have hj : i < (l.map f).length := by simpa using hi
  simp only [List.getD_eq_getElem?_getD, getElem?_pos (l.map f) i hj, getElem?_pos l i hi,
    Option.getD_some, List.getElem_map]

private theorem getD_mem_of_lt {α : Type*} (l : List α) (i : ℕ) (d : α) (hi : i < l.length) :
    l.getD i d ∈ l := by
  simpa only [List.getD_eq_getElem?_getD, getElem?_pos l i hi, Option.getD_some,
    List.get_eq_getElem] using l.get_mem ⟨i, hi⟩

private theorem getD_boundedWords_eq (c : RationalFeedbackCode)
    (i : Fin (c.boundedWords c.1).length) :
    (c.boundedWords c.1).getD i.val [] = (c.boundedWordAt c.1 i).map Fin.val := by
  simp only [boundedWordAt_map_val, List.getD_eq_getElem?_getD,
    getElem?_pos (c.boundedWords c.1) i.val i.isLt, Option.getD_some, List.get_eq_getElem]

private theorem tableEntry_eq_wordOutput (c : RationalFeedbackCode)
    (i j : Fin (c.boundedWords c.1).length) :
    tableEntry c.hankelEliminationTable i.val j.val =
      c.representation.output (c.representation.wordAction
        (c.boundedWordAt c.1 i ++ c.boundedWordAt c.1 j) c.representation.initial) := by
  change (c.wordHankel c.1 []).getD (i.val * (c.boundedWords c.1).length + j.val) 0 = _
  rw [wordHankel_getD]
  simpa only [List.map_nil, LinearRepresentation.wordAction_nil,
    LinearRepresentation.wordAction_append] using c.wordHankelEntry_eq c.1 [] i j

set_option maxHeartbeats 900000 in
/-- Elimination computes a rational encoding of the exact reachable/observable
quotient, preserving the specified order of the generating operators. -/
theorem gaussianQuotient_correct (c : RationalFeedbackCode)
    (hcomm : ∀ i j, Commute (c.operator i) (c.operator j)) :
    wordOutputsAgree (c, c.gaussianQuotient) ∧
      (∀ i j, Commute (c.gaussianQuotient.operator i) (c.gaussianQuotient.operator j)) ∧
      c.gaussianQuotient.representation.reachable = ⊤ ∧
      Submodule.span ℚ (Set.range fun w => c.gaussianQuotient.representation.output.comp
        (c.gaussianQuotient.representation.wordAction w)) = ⊤ := by
  let t := c.hankelEliminationTable
  let s := eliminate t
  let p := c.coordinatesOfSelection s
  let N := (c.boundedWords c.1).length
  have hs : ValidSelection t s := eliminate_valid t
  have hcLen : p.dimension = s.2.1.length := by
    simp [p, coordinatesOfSelection, QuotientCoordinateData.dimension, selectedWords]
  have hrLen : p.dimension = s.1.length := hcLen.trans hs.sizes
  let e : Fin p.dimension ≃ Fin s.1.length := finCongr hrLen
  let r (i : Fin p.dimension) : Fin N :=
    ⟨s.1.getD i.val 0, hs.rows_inRange _ (getD_mem_of_lt _ _ _ (hrLen ▸ i.isLt))⟩
  let q (j : Fin p.dimension) : Fin N :=
    ⟨s.2.1.getD j.val 0, hs.cols_inRange _ (getD_mem_of_lt _ _ _ (hcLen ▸ j.isLt))⟩
  let u := c.boundedWordAt c.1 ∘ r
  let v := c.boundedWordAt c.1 ∘ q
  let H := selectedMatrix t s
  let R := GaussianPivot.matrixOfEntries s.1.length s.2.2
  have hH : c.representation.wordHankel u v = H.submatrix e e := by
    ext i j
    exact (tableEntry_eq_wordOutput c (r i) (q j)).symm
  have hR : p.inverseMatrix = R.submatrix e e := by
    ext i j
    change s.2.2.getD (i.val * p.dimension + j.val) 0 =
      s.2.2.getD (i.val * s.1.length + j.val) 0
    exact congrArg (fun n => s.2.2.getD (i.val * n + j.val) 0) hrLen
  have hHR' : H * R = 1 := hs.inverse
  have hRH' : R * H = 1 := mul_eq_one_comm.mp hHR'
  have hHR : c.representation.wordHankel u v * p.inverseMatrix = 1 := by
    rw [hH, hR, Matrix.submatrix_mul_equiv, hHR', Matrix.submatrix_one_equiv]
  have hRH : p.inverseMatrix * c.representation.wordHankel u v = 1 := by
    rw [hH, hR, Matrix.submatrix_mul_equiv, hRH', Matrix.submatrix_one_equiv]
  let M (a b : Fin N) := tableEntry t a.val b.val
  have hSelected : (Matrix.of (fun i j => M (r i) (q j))) =
      c.representation.wordHankel u v := by
    ext i j
    exact tableEntry_eq_wordOutput c (r i) (q j)
  have hFactor : ∀ a b, M a b =
      ∑ j, M a (q j) * (p.inverseMatrix.mulVec (fun i => M (r i) b)) j := by
    apply entry_eq_selectedBlock_factorization M r q p.inverseMatrix
      (by rw [hSelected]; exact hHR) (by rw [hSelected]; exact hRH)
    intro a ha b hb
    have har : a.val ∉ s.1 := by
      intro hh
      obtain ⟨i, hi, he⟩ := List.getElem_of_mem hh
      apply ha
      refine ⟨⟨i, hrLen.symm ▸ hi⟩, Fin.ext ?_⟩
      simpa only [r, List.getD_eq_getElem?_getD, getElem?_pos s.1 i hi, Option.getD_some] using he
    have hbq : b.val ∉ s.2.1 := by
      intro hh
      obtain ⟨j, hj, he⟩ := List.getElem_of_mem hh
      apply hb
      refine ⟨⟨j, hcLen.symm ▸ hj⟩, Fin.ext ?_⟩
      simpa only [q, List.getD_eq_getElem?_getD, getElem?_pos s.2.1 j hj, Option.getD_some] using he
    let d := pivotData t s a.val b.val
    have hz : GaussianPivot.schurComplement d = 0 :=
      all_remaining_schur_zero t a.val b.val a.isLt b.isLt har hbq
    rw [GaussianPivot.schurComplement_eq_sub_mulVec] at hz
    let X (i : Fin s.1.length) := d.2.2.1.getD i.val 0
    have hX : X ∘ e = fun i => M (r i) b := by
      funext i
      have hi : i.val < s.1.length := hrLen ▸ i.isLt
      exact getD_map_of_lt hi (fun k => tableEntry t k b.val) 0 0
    have hSolve : p.inverseMatrix.mulVec (fun i => M (r i) b) = (R.mulVec X) ∘ e := by
      rw [hR, ← hX, Matrix.submatrix_mulVec_equiv]
      simp [Function.comp_def]
    rw [hSolve]
    have hSum : (∑ j : Fin p.dimension, M a (q j) * ((R.mulVec X) ∘ e) j) =
        ∑ j : Fin s.1.length, d.2.2.2.1.getD j.val 0 * (R.mulVec X) j := by
      refine Fintype.sum_equiv e _ _ (fun j => ?_)
      have hj : j.val < s.2.1.length := hcLen ▸ j.isLt
      rw [show d.2.2.2.1.getD (e j).val 0 = M a (q j) from
        getD_map_of_lt hj (tableEntry t a.val) 0 0]
      rfl
    rw [hSum]
    exact sub_eq_zero.mp hz
  have hResid (a b : List (Fin c.2.2.2.length)) (ha : a.length ≤ c.1) (hb : b.length ≤ c.1) :
      c.representation.output (c.representation.wordAction (a ++ b) c.representation.initial) =
        ∑ j, c.representation.output (c.representation.wordAction (a ++ v j) c.representation.initial) *
          (p.inverseMatrix.mulVec (c.representation.wordObservations u b)) j := by
    obtain ⟨i, rfl⟩ := c.exists_boundedWordAt_eq c.1 a ha
    obtain ⟨j, rfl⟩ := c.exists_boundedWordAt_eq c.1 b hb
    have hEntry (a b : Fin N) : M a b =
        c.representation.output (c.representation.wordAction
          (c.boundedWordAt c.1 a ++ c.boundedWordAt c.1 b) c.representation.initial) :=
      tableEntry_eq_wordOutput c a b
    have hObservation : (fun k => M (r k) j) =
        c.representation.wordObservations u (c.boundedWordAt c.1 j) := by
      funext k
      exact hEntry (r k) j
    have h := hFactor i j
    rw [hObservation] at h
    simpa only [hEntry, v, Function.comp_apply] using h
  have hRow (i : Fin p.dimension) : p.2.1.getD i.val [] = (u i).map Fin.val := by
    have hi : i.val < s.1.length := hrLen ▸ i.isLt
    exact (getD_map_of_lt hi (fun k => (c.boundedWords c.1).getD k []) 0 []).trans
      (getD_boundedWords_eq c (r i))
  have hCol (i : Fin p.dimension) : p.2.2.1.getD i.val [] = (v i).map Fin.val := by
    have hi : i.val < s.2.1.length := hcLen ▸ i.isLt
    exact (getD_map_of_lt hi (fun k => (c.boundedWords c.1).getD k []) 0 []).trans
      (getD_boundedWords_eq c (q i))
  exact p.quotientCode_correct u v hRow hCol hHR hRH hResid hcomm

end ContinuousBilinear.RationalFeedbackCode
