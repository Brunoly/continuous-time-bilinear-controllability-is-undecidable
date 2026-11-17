import ContinuousBilinear.CompilerGaussianPivotProof

namespace ContinuousBilinear.GaussianElimination

open GaussianPivot

/-- Row count, column count and row-major coefficients of a rational matrix. -/
abbrev Table := ℕ × ℕ × List ℚ

/-- Selected row and column indices and the current square inverse, row-major. -/
abbrev Selection := List ℕ × List ℕ × List ℚ

def tableEntry (t : Table) (i j : ℕ) : ℚ := entry t.2.1 t.2.2 i j

def selectedMatrix (t : Table) (s : Selection) : Matrix (Fin s.1.length) (Fin s.1.length) ℚ :=
  Matrix.of fun i j => tableEntry t (s.1.getD i.val 0) (s.2.1.getD j.val 0)

abbrev pivotData (t : Table) (s : Selection) (i j : ℕ) : Data :=
  (s.1.length, s.2.2, s.1.map (fun k => tableEntry t k j),
    s.2.1.map (fun l => tableEntry t i l), tableEntry t i j)

def candidates (t : Table) : List (ℕ × ℕ) :=
  (List.range t.1).flatMap fun i => (List.range t.2.1).map (i, ·)

private theorem mem_candidates (t : Table) (i j : ℕ) :
    (i,j) ∈ candidates t ↔ i < t.1 ∧ j < t.2.1 := by
  simp [candidates, List.mem_flatMap]

def eligible (t : Table) (s : Selection) (i j : ℕ) : Bool :=
  decide (i ∉ s.1 ∧ j ∉ s.2.1 ∧ schurComplement (pivotData t s i j) ≠ 0)

def nextPivot (t : Table) (s : Selection) : Option (ℕ × ℕ) :=
  (candidates t).find? (fun ij => eligible t s ij.1 ij.2)

def extend (t : Table) (s : Selection) (i j : ℕ) : Selection :=
  (s.1 ++ [i], s.2.1 ++ [j], borderedInverse (pivotData t s i j))

def advance (t : Table) (s : Selection) : Selection :=
  match nextPivot t s with
  | none => s
  | some (i,j) => extend t s i j

def stages (t : Table) : ℕ → Selection
  | 0 => ([], [], [])
  | k + 1 => advance t (stages t k)

/-- Bounded rational Gaussian elimination, retaining original row and column indices. -/
def eliminate (t : Table) : Selection := stages t t.1

/-- The current selected submatrix and its inverse have matching dimensions,
and the selected indices are distinct and in the original ranges. -/
structure ValidSelection (t : Table) (s : Selection) : Prop where
  sizes : s.2.1.length = s.1.length
  rows_nodup : s.1.Nodup
  cols_nodup : s.2.1.Nodup
  rows_inRange : ∀ i ∈ s.1, i < t.1
  cols_inRange : ∀ j ∈ s.2.1, j < t.2.1
  inverse : selectedMatrix t s * matrixOfEntries s.1.length s.2.2 = 1

private theorem getD_extend_lt {xs : List ℕ} {i : ℕ} (h : i < xs.length) (x : ℕ) :
    (xs ++ [x]).getD i 0 = xs.getD i 0 := by
  have h' : i < (xs ++ [x]).length := by simp; omega
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    getElem?_pos (xs ++ [x]) i h', getElem?_pos xs i h, List.getElem_append_left h]

private theorem getD_extend_last (xs : List ℕ) (x : ℕ) : (xs ++ [x]).getD xs.length 0 = x := by
  have h : xs.length < (xs ++ [x]).length := by simp
  rw [List.getD_eq_getElem?_getD, getElem?_pos (xs ++ [x]) xs.length h, List.getElem_append_right le_rfl]
  simp

private theorem getD_map_of_lt {α β : Type*} {xs : List α} {i : ℕ} (h : i < xs.length)
    (f : α → β) (x : α) (y : β) : (xs.map f).getD i y = f (xs.getD i x) := by
  have h' : i < (xs.map f).length := by simpa using h
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, getElem?_pos (xs.map f) i h',
    getElem?_pos xs i h, List.getElem_map]
  rfl

private theorem extend_length (t : Table) (s : Selection) (i j : ℕ) :
    (extend t s i j).1.length = s.1.length + 1 := by simp [extend]

private theorem selectedMatrix_extend (t : Table) (s : Selection) (i j : ℕ)
    (hs : s.2.1.length = s.1.length) :
    (selectedMatrix t (extend t s i j)).submatrix
        (finCongr (extend_length t s i j)).symm (finCongr (extend_length t s i j)).symm =
      borderedMatrix (pivotData t s i j) (selectedMatrix t s) := by
  let e : Fin s.1.length ⊕ Fin 1 ≃ Fin (s.1.length + 1) := finSumFinEquiv
  apply Matrix.ext
  intro a b
  obtain ⟨a, rfl⟩ := e.surjective a
  obtain ⟨b, rfl⟩ := e.surjective b
  refine Eq.trans ?_ (borderedMatrix_entry (pivotData t s i j) (selectedMatrix t s) a b).symm
  have hval (k : Fin (s.1.length + 1)) :
      ((finCongr (extend_length t s i j)).symm k).val = k.val := rfl
  rw [Matrix.submatrix_apply]
  change tableEntry t ((s.1 ++ [i]).getD _ 0) ((s.2.1 ++ [j]).getD _ 0) = _
  rw [hval, hval]
  have hl (k : Fin s.1.length) : (e (Sum.inl k)).val = k.val := rfl
  have hr (k : Fin 1) : (e (Sum.inr k)).val = s.1.length := by
    obtain rfl : k = 0 := Subsingleton.elim _ _
    simp [e, finSumFinEquiv_apply_right]
  have he : (s.2.1 ++ [j]).getD s.1.length 0 = j := hs ▸ getD_extend_last s.2.1 j
  rcases a with a | a <;> rcases b with b | b
  · rw [hl, hl, getD_extend_lt a.isLt i, getD_extend_lt (hs.symm ▸ b.isLt) j]
    rfl
  · rw [hl, hr, getD_extend_lt a.isLt i, he]
    exact (getD_map_of_lt a.isLt (fun k => tableEntry t k j) 0 0).symm
  · rw [hr, hl, getD_extend_last, getD_extend_lt (hs.symm ▸ b.isLt) j]
    exact (getD_map_of_lt (hs.symm ▸ b.isLt) (tableEntry t i) 0 0).symm
  · rw [hr, hr, getD_extend_last]
    rw [he]
    rfl

private theorem matrixOfEntries_extend (t : Table) (s : Selection) (i j : ℕ) :
    (matrixOfEntries (extend t s i j).1.length (extend t s i j).2.2).submatrix
        (finCongr (extend_length t s i j)).symm (finCongr (extend_length t s i j)).symm =
      matrixOfEntries (s.1.length + 1) (borderedInverse (pivotData t s i j)) := by
  apply Matrix.ext
  intro a b
  change (borderedInverse (pivotData t s i j)).getD
    (a.val * (extend t s i j).1.length + b.val) 0 =
      (borderedInverse (pivotData t s i j)).getD (a.val * (s.1.length + 1) + b.val) 0
  rw [extend_length]

private theorem validSelection_extend (t : Table) (s : Selection) (i j : ℕ)
    (hs : ValidSelection t s) (hi : i < t.1) (hj : j < t.2.1)
    (hrow : i ∉ s.1) (hcol : j ∉ s.2.1) (hp : schurComplement (pivotData t s i j) ≠ 0) :
    ValidSelection t (extend t s i j) := by
  have hn {xs : List ℕ} (hx : xs.Nodup) {x : ℕ} (hn : x ∉ xs) : (xs ++ [x]).Nodup := by
    refine List.nodup_append.mpr ⟨hx, by simp, ?_⟩
    intro a ha b hb he
    have hbx : b = x := by simpa using hb
    exact hn (he.trans hbx ▸ ha)
  have hr {xs : List ℕ} {k x : ℕ} (hx : ∀ y ∈ xs, y < k) (h : x < k) :
      ∀ y ∈ xs ++ [x], y < k := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact hx _ hy
    · have he : y = x := by simpa using hy
      simpa only [he] using h
  refine ⟨by simp [extend, hs.sizes], hn hs.rows_nodup hrow, hn hs.cols_nodup hcol,
    hr hs.rows_inRange hi, hr hs.cols_inRange hj, ?_⟩
  let e := (finCongr (extend_length t s i j)).symm
  have he := (borderedInverse_correct (pivotData t s i j) (selectedMatrix t s) hs.inverse hp).1
  have h' :
      (selectedMatrix t (extend t s i j) *
        matrixOfEntries (extend t s i j).1.length (extend t s i j).2.2).submatrix e e =
        (1 : Matrix (Fin (s.1.length + 1)) (Fin (s.1.length + 1)) ℚ) := by
    rw [← Matrix.submatrix_mul_equiv (selectedMatrix t (extend t s i j))
      (matrixOfEntries (extend t s i j).1.length (extend t s i j).2.2) e e e]
    exact (congrArg₂ (· * ·) (selectedMatrix_extend t s i j hs.sizes)
      (matrixOfEntries_extend t s i j)).trans he
  have h'' := congrArg (fun A : Matrix (Fin (s.1.length + 1)) (Fin (s.1.length + 1)) ℚ =>
    A.submatrix e.symm e.symm) h'
  simpa only [Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id,
    Matrix.submatrix_one_equiv] using h''

private theorem validSelection_advance (t : Table) (s : Selection) (hs : ValidSelection t s) :
    ValidSelection t (advance t s) := by
  unfold advance
  cases h : nextPivot t s with
  | none => exact hs
  | some ij =>
    rcases ij with ⟨i, j⟩
    have hl := (mem_candidates t i j).mp (List.mem_of_find?_eq_some h)
    have hfind : (candidates t).find? (fun ij : ℕ × ℕ => eligible t s ij.1 ij.2) = some (i, j) := h
    have he : eligible t s i j = true :=
      List.find?_some (a := (i, j)) (p := fun ij : ℕ × ℕ => eligible t s ij.1 ij.2) hfind
    have hp : i ∉ s.1 ∧ j ∉ s.2.1 ∧ schurComplement (pivotData t s i j) ≠ 0 :=
      of_decide_eq_true he
    exact validSelection_extend t s i j hs hl.1 hl.2 hp.1 hp.2.1 hp.2.2

theorem stages_valid (t : Table) (k : ℕ) : ValidSelection t (stages t k) := by
  induction k with
  | zero =>
    refine ⟨rfl, by simp [stages], by simp [stages], by simp [stages], by simp [stages], ?_⟩
    change (_ : Matrix (Fin 0) (Fin 0) ℚ) = _
    exact Subsingleton.elim _ _
  | succ k ih => exact validSelection_advance t _ ih

theorem eliminate_valid (t : Table) : ValidSelection t (eliminate t) := stages_valid t _

private theorem advance_eq_self_of_none (t : Table) (s : Selection)
    (h : nextPivot t s = none) : advance t s = s := by simp [advance, h]

private theorem stages_terminal_persists (t : Table) {k l : ℕ} (hkl : k ≤ l)
    (hk : nextPivot t (stages t k) = none) : stages t l = stages t k := by
  induction hkl with
  | refl => rfl
  | step h ih =>
    rw [stages, ih]
    exact advance_eq_self_of_none t _ hk

theorem eliminate_terminal (t : Table) : nextPivot t (eliminate t) = none := by
  by_contra hend
  have hall (k : ℕ) (hk : k ≤ t.1) : nextPivot t (stages t k) ≠ none := by
    intro h
    exact hend (by unfold eliminate; rw [stages_terminal_persists t hk h]; exact h)
  have hsize (k : ℕ) (hk : k ≤ t.1 + 1) : (stages t k).1.length = k := by
    induction k with
    | zero => rfl
    | succ k ih =>
      have hsize := ih (by omega)
      have hfound := hall k (by omega)
      rw [stages]
      unfold advance
      cases h : nextPivot t (stages t k) with
      | none => exact (hfound h).elim
      | some ij =>
        rcases ij with ⟨i, j⟩
        exact (extend_length t _ i j).trans (by omega)
  have hs := stages_valid t (t.1 + 1)
  have hsub : (stages t (t.1 + 1)).1 ⊆ List.range t.1 :=
    fun i hi => List.mem_range.mpr (hs.rows_inRange i hi)
  have hle := hs.rows_nodup.length_le_of_subset hsub
  rw [List.length_range, hsize _ le_rfl] at hle
  omega

/-- At termination, no row and column outside the selected sets has a nonzero pivot. -/
theorem all_remaining_schur_zero (t : Table) (i j : ℕ) (hi : i < t.1) (hj : j < t.2.1)
    (hrow : i ∉ (eliminate t).1) (hcol : j ∉ (eliminate t).2.1) :
    schurComplement (pivotData t (eliminate t) i j) = 0 := by
  have ht := eliminate_terminal t
  unfold nextPivot at ht
  have hfalse := List.find?_eq_none.mp ht (i, j) ((mem_candidates t i j).mpr ⟨hi, hj⟩)
  by_contra hp
  exact hfalse (decide_eq_true ⟨hrow, hcol, hp⟩)

end ContinuousBilinear.GaussianElimination
