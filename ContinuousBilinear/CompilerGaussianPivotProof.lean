import ContinuousBilinear.CompilerGaussianArithmeticProof
import Mathlib.LinearAlgebra.Matrix.SchurComplement

namespace ContinuousBilinear.GaussianPivot

open Matrix

def column (p : Data) : Matrix (Fin p.1) (Fin 1) ℚ :=
  Matrix.of fun i _ => p.2.2.1.getD i.val 0

def row (p : Data) : Matrix (Fin 1) (Fin p.1) ℚ :=
  Matrix.of fun _ j => p.2.2.2.1.getD j.val 0

def singleton (x : ℚ) : Matrix (Fin 1) (Fin 1) ℚ := Matrix.of fun _ _ => x

private abbrev splitIndex (n : ℕ) : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv

/-- Border a square matrix, with the added row and column last. -/
def borderedMatrix (p : Data) (A : Matrix (Fin p.1) (Fin p.1) ℚ) :
    Matrix (Fin (p.1 + 1)) (Fin (p.1 + 1)) ℚ :=
  (fromBlocks A (column p) (row p) (singleton p.2.2.2.2)).submatrix
    (splitIndex p.1).symm (splitIndex p.1).symm

private theorem inverseColumn_eq (p : Data) (i : Fin p.1) (j : Fin 1) :
    (matrixOfEntries p.1 p.2.1 * column p) i j = inverseColumn p i.val := by
  rw [Matrix.mul_apply, inverseColumn, sumProducts_eq_sum]
  rfl

private theorem rowInverse_eq (p : Data) (i : Fin 1) (j : Fin p.1) :
    (row p * matrixOfEntries p.1 p.2.1) i j = rowInverse p j.val := by
  rw [Matrix.mul_apply, rowInverse, sumProducts_eq_sum]
  rfl

theorem schurComplement_eq_sub_mulVec (p : Data) :
    schurComplement p = p.2.2.2.2 - ∑ j : Fin p.1, p.2.2.2.1.getD j.val 0 *
      (matrixOfEntries p.1 p.2.1).mulVec (fun i => p.2.2.1.getD i.val 0) j := by
  rw [schurComplement, sumProducts_eq_sum]
  apply congrArg (p.2.2.2.2 - ·)
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (p.2.2.2.1.getD j.val 0 * ·) (inverseColumn_eq p j 0).symm

private theorem singleton_schur (p : Data) :
    singleton (schurComplement p) =
      singleton p.2.2.2.2 - row p * matrixOfEntries p.1 p.2.1 * column p := by
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_assoc, Matrix.sub_apply, Matrix.mul_apply, schurComplement, sumProducts_eq_sum]
  simp only [singleton, Matrix.of_apply, inverseColumn_eq, row]

private theorem singleton_mul (x y : ℚ) : singleton x * singleton y = singleton (x * y) := by
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_one]
  rfl

private theorem singleton_one : singleton 1 = 1 := by
  apply Matrix.ext
  intro i j
  rw [Subsingleton.elim i j, Matrix.one_apply_eq]
  rfl

private theorem splitIndex_left (n : ℕ) (i : Fin n) :
    ((splitIndex n) (Sum.inl i)).val = i.val := rfl

private theorem splitIndex_right (n : ℕ) (i : Fin 1) :
    ((splitIndex n) (Sum.inr i)).val = n := by
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp [finSumFinEquiv_apply_right]

theorem borderedMatrix_entry (p : Data) (A : Matrix (Fin p.1) (Fin p.1) ℚ)
    (i j : Fin p.1 ⊕ Fin 1) :
    borderedMatrix p A ((splitIndex p.1) i) ((splitIndex p.1) j) =
      (fromBlocks A (column p) (row p) (singleton p.2.2.2.2)) i j := by
  simp only [borderedMatrix, Matrix.submatrix_apply, Equiv.symm_apply_apply]

private theorem borderedInverse_entry (p : Data) (i j : Fin (p.1 + 1)) :
    matrixOfEntries (p.1 + 1) (borderedInverse p) i j = borderedEntry p i.val j.val := by
  let A : Matrix (Fin (p.1 + 1)) (Fin (p.1 + 1)) ℚ :=
    Matrix.of fun i j => borderedEntry p i.val j.val
  have h : borderedInverse p = PlantCode.matrixEntries A := by
    unfold borderedInverse
    exact PlantCode.tabulateMatrix_eq_matrixEntries _ _ (fun _ _ => rfl)
  rw [h]
  exact PlantCode.matrixEntries_getD A i j 0

private theorem inverse_blocks (p : Data) :
    let X := matrixOfEntries p.1 p.2.1
    let R := singleton ((schurComplement p)⁻¹)
    (matrixOfEntries (p.1 + 1) (borderedInverse p)).submatrix (splitIndex p.1) (splitIndex p.1) =
      fromBlocks (X + X * column p * R * row p * X)
        (-(X * column p * R)) (-(R * row p * X)) R := by
  dsimp only
  let X := matrixOfEntries p.1 p.2.1
  let R := singleton ((schurComplement p)⁻¹)
  have hcol (i : Fin p.1) (j : Fin 1) :
      (X * column p * R) i j = inverseColumn p i.val * (schurComplement p)⁻¹ := by
    rw [Matrix.mul_apply, Fin.sum_univ_one]
    exact congrArg (fun a => a * (schurComplement p)⁻¹) (inverseColumn_eq p i 0)
  have hrow (i : Fin 1) (j : Fin p.1) :
      (R * (row p * X)) i j = (schurComplement p)⁻¹ * rowInverse p j.val := by
    rw [Matrix.mul_apply, Fin.sum_univ_one]
    exact congrArg (fun a => (schurComplement p)⁻¹ * a) (rowInverse_eq p 0 j)
  have hboth (i j : Fin p.1) :
      ((X * column p * R) * (row p * X)) i j =
        (inverseColumn p i.val * (schurComplement p)⁻¹) * rowInverse p j.val := by
    rw [Matrix.mul_apply, Fin.sum_univ_one, hcol, rowInverse_eq]
  have hform :
      (fromBlocks (X + X * column p * R * row p * X)
        (-(X * column p * R)) (-(R * row p * X)) R :
        Matrix (Fin p.1 ⊕ Fin 1) (Fin p.1 ⊕ Fin 1) ℚ) =
      fromBlocks (X + (X * column p * R) * (row p * X))
        (-(X * column p * R)) (-(R * (row p * X))) R := by simp only [Matrix.mul_assoc]
  change _ = fromBlocks (X + X * column p * R * row p * X)
    (-(X * column p * R)) (-(R * row p * X)) R
  rw [hform]
  apply Matrix.ext
  intro i j
  rw [Matrix.submatrix_apply, borderedInverse_entry]
  rcases i with i | i <;> rcases j with j | j
  · simp only [splitIndex_left, borderedEntry, i.isLt, j.isLt, ite_true, Matrix.fromBlocks_apply₁₁,
      Matrix.add_apply, hboth]
    rfl
  · simp only [splitIndex_left, splitIndex_right, borderedEntry, i.isLt, lt_irrefl, ite_true,
      ite_false, Matrix.fromBlocks_apply₁₂, Matrix.neg_apply, hcol]
  · simp only [splitIndex_left, splitIndex_right, borderedEntry, j.isLt, lt_irrefl, ite_true,
      ite_false, Matrix.fromBlocks_apply₂₁, Matrix.neg_apply, hrow]
  · simp only [splitIndex_right, borderedEntry, lt_irrefl, ite_false, Matrix.fromBlocks_apply₂₂]
    rfl

/-- Under the inverse invariant, a nonzero Schur pivot exactly detects nonsingularity
of the enlarged square matrix. -/
theorem det_borderedMatrix_ne_zero_iff (p : Data) (A : Matrix (Fin p.1) (Fin p.1) ℚ)
    (hA : A * matrixOfEntries p.1 p.2.1 = 1) :
    (borderedMatrix p A).det ≠ 0 ↔ schurComplement p ≠ 0 := by
  let X := matrixOfEntries p.1 p.2.1
  let _ : Invertible A := ⟨X, (mul_eq_one_comm.mp hA), hA⟩
  have hs : ⅟A = X := rfl
  have hdet : A.det ≠ 0 := isUnit_iff_ne_zero.mp (Matrix.isUnit_det_of_invertible A)
  rw [borderedMatrix, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks₁₁, hs,
    ← singleton_schur, Matrix.det_fin_one]
  change A.det * schurComplement p ≠ 0 ↔ schurComplement p ≠ 0
  exact ⟨fun h hs => h (by rw [hs, mul_zero]), mul_ne_zero hdet⟩

/-- The rational row-major update is an exact inverse after a nonzero Schur pivot. -/
theorem borderedInverse_correct (p : Data) (A : Matrix (Fin p.1) (Fin p.1) ℚ)
    (hA : A * matrixOfEntries p.1 p.2.1 = 1) (h : schurComplement p ≠ 0) :
    borderedMatrix p A * matrixOfEntries (p.1 + 1) (borderedInverse p) = 1 ∧
      matrixOfEntries (p.1 + 1) (borderedInverse p) * borderedMatrix p A = 1 := by
  let X := matrixOfEntries p.1 p.2.1
  let s := schurComplement p
  let R := singleton s⁻¹
  let S := singleton p.2.2.2.2 - row p * X * column p
  let B := fromBlocks A (column p) (row p) (singleton p.2.2.2.2)
  let Y := matrixOfEntries (p.1 + 1) (borderedInverse p)
  let e := splitIndex p.1
  let _ : Invertible A := ⟨X, mul_eq_one_comm.mp hA, hA⟩
  have hS : S = singleton s := (singleton_schur p).symm
  let _ : Invertible S :=
    ⟨R, by rw [hS, singleton_mul, inv_mul_cancel₀ h, singleton_one],
      by rw [hS, singleton_mul, mul_inv_cancel₀ h, singleton_one]⟩
  let _ : Invertible B := fromBlocks₁₁Invertible A (column p) (row p) (singleton p.2.2.2.2)
  have hY : Y.submatrix e e = ⅟B := by
    rw [inverse_blocks p]
    exact (invOf_fromBlocks₁₁_eq A (column p) (row p) (singleton p.2.2.2.2)).symm
  have hBY : B * Y.submatrix e e = 1 := by rw [hY, mul_invOf_self]
  have hi : (borderedMatrix p A * Y).submatrix e e = 1 := by
    rw [← Matrix.submatrix_mul_equiv (borderedMatrix p A) Y e e e]
    change (B.submatrix e.symm e.symm).submatrix e e * _ = _
    simpa only [Matrix.submatrix_submatrix, Equiv.symm_comp_self, Matrix.submatrix_id_id]
      using hBY
  have ht : borderedMatrix p A * Y = 1 := by
    have h' := congrArg (fun M : Matrix (Fin p.1 ⊕ Fin 1) (Fin p.1 ⊕ Fin 1) ℚ =>
      M.submatrix e.symm e.symm) hi
    simpa only [Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id,
      Matrix.submatrix_one_equiv] using h'
  exact ⟨ht, mul_eq_one_comm.mp ht⟩

end ContinuousBilinear.GaussianPivot
