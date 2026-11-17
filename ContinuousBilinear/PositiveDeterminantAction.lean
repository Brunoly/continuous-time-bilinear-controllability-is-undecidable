import ContinuousBilinear.TransitionProducts
import Mathlib.LinearAlgebra.Determinant

namespace ContinuousBilinear

private theorem exists_basis_with_vector {n : ℕ} (i : Fin n) (x : State n) (hx : x ≠ 0) :
    ∃ b : Module.Basis (Fin n) ℝ (State n), b i = x := by
  classical
  have h : LinearIndepOn ℝ id ({x} : Set (State n)) :=
    LinearIndepOn.singleton hx
  let b := Module.Basis.extend h
  let j : h.extend (Set.subset_univ _) := ⟨x, h.subset_extend _ (Set.mem_singleton x)⟩
  let := b.fintypeIndexOfRankLtAleph0 (Module.rank_lt_aleph0 ℝ (State n))
  have hcard : Fintype.card (h.extend (Set.subset_univ _)) = Fintype.card (Fin n) := by
    rw [← Module.finrank_eq_card_basis b, Module.finrank_fin_fun, Fintype.card_fin]
  let e := Fintype.equivOfCardEq hcard
  let e' := e.trans (Equiv.swap (e j) i)
  have hj : e' j = i := by simp [e']
  refine ⟨b.reindex e', ?_⟩
  rw [← hj, Module.Basis.reindex_apply, Equiv.symm_apply_apply]
  exact Module.Basis.extend_apply_self h j

private theorem exists_positive_matrix_with_column {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (x : State n) (hx : x ≠ 0) :
    ∃ A : RealMatrix n, 0 < A.det ∧ A.mulVec (Pi.single i 1) = x := by
  classical
  obtain ⟨b, hb⟩ := exists_basis_with_vector i x hx
  let A : RealMatrix n := (Matrix.of b).transpose
  have hdet : A.det ≠ 0 := by
    rw [show A.det = (Matrix.of b).det by exact Matrix.det_transpose _,
        ← Pi.basisFun_det_apply]
    exact ((Pi.basisFun ℝ (Fin n)).isUnit_det b).ne_zero
  have hA : A.mulVec (Pi.single i 1) = x := by
    rw [Matrix.mulVec_single_one]
    exact hb
  rcases lt_or_gt_of_ne hdet with hneg | hpos
  · let D : RealMatrix n := Matrix.diagonal (fun k => if k = j then -1 else 1)
    have hDdet : D.det = -1 := by
      simp [D, Matrix.det_diagonal]
    refine ⟨A * D, ?_, ?_⟩
    · rw [Matrix.det_mul, hDdet, mul_neg_one]
      exact neg_pos.mpr hneg
    · have hD : D.mulVec (Pi.single i 1) = Pi.single i 1 := by
        simp [D, hij]
      rwa [← Matrix.mulVec_mulVec, hD]
  · exact ⟨A, hpos, hA⟩

/-- Positive-determinant matrices act transitively on the punctured space in dimension at least two. -/
theorem exists_pos_det_mulVec_eq {n : ℕ} (hn : 2 ≤ n) (x y : State n)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ A : RealMatrix n, 0 < A.det ∧ A.mulVec x = y := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := fun h => Nat.zero_ne_one (congrArg Fin.val h)
  obtain ⟨A, hA, hAx⟩ := exists_positive_matrix_with_column i j hij x hx
  obtain ⟨B, hB, hBy⟩ := exists_positive_matrix_with_column i j hij y hy
  obtain ⟨U, rfl⟩ := (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hA.ne')
  have hInv : 0 < (↑U⁻¹ : RealMatrix n).det := by
    have hprod : (↑U⁻¹ : RealMatrix n).det * (↑U : RealMatrix n).det = 1 := by
      rw [← Matrix.det_mul, Units.inv_mul, Matrix.det_one]
    exact pos_of_mul_pos_left (hprod ▸ zero_lt_one) hA.le
  refine ⟨B * ↑U⁻¹, by rw [Matrix.det_mul]; exact mul_pos hB hInv, ?_⟩
  rw [← hAx, Matrix.mulVec_mulVec, mul_assoc, Units.inv_mul, mul_one, hBy]

end ContinuousBilinear
