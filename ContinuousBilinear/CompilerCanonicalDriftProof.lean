import ContinuousBilinear.Feedback
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace ContinuousBilinear

namespace FeedbackCoordinates

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] {n : ℕ}

/-- Columns are the rank-one drift vector followed by a basis for the kernel
of its output row. The scalar coordinate comes first. -/
def basisMatrix (b ell : Fin n → 𝕜) : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜 :=
  Matrix.of (Fin.cases (Fin.cases 1 (fun j => -ell j))
    (fun i => Fin.cases (b i) (fun j => if i = j then 1 else 0)))

/-- The inverse recovers the first coordinate via the normalized output row. -/
def inverseMatrix (b ell : Fin n → 𝕜) : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜 :=
  Matrix.of (Fin.cases (Fin.cases (1 / 2) (fun j => (1 / 2) * ell j))
    (fun i => Fin.cases (-(b i * (1 / 2)))
      (fun j => (if i = j then 1 else 0) - (b i * (1 / 2)) * ell j)))

def rankOneDrift (b ell : Fin n → 𝕜) : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜 :=
  Matrix.of fun i j => (1 / 2) * Fin.cases 1 b i * Fin.cases 1 ell j

def canonicalDrift (n : ℕ) : Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜 :=
  Matrix.diagonal fun i => if i.val = 0 then 1 else 0

private def tailPairing (ell : Fin n → 𝕜) (v : Fin (n + 1) → 𝕜) : 𝕜 :=
  ∑ j : Fin n, ell j * v j.succ

private theorem basis_mulVec_zero (b ell : Fin n → 𝕜) (v : Fin (n+1) → 𝕜) :
    (basisMatrix b ell).mulVec v 0 = v 0 - tailPairing ell v := by
  simp [basisMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, tailPairing,
    Finset.sum_neg_distrib, sub_eq_add_neg]

private theorem basis_mulVec_succ (b ell : Fin n → 𝕜) (v : Fin (n+1) → 𝕜) (i : Fin n) :
    (basisMatrix b ell).mulVec v i.succ = b i * v 0 + v i.succ := by
  simp [basisMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, ite_mul]

private theorem inverse_mulVec_zero (b ell : Fin n → 𝕜) (v : Fin (n+1) → 𝕜) :
    (inverseMatrix b ell).mulVec v 0 = (1 / 2) * (v 0 + tailPairing ell v) := by
  simp [inverseMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, tailPairing,
    mul_add, Finset.mul_sum, mul_assoc]

private theorem inverse_mulVec_succ (b ell : Fin n → 𝕜) (v : Fin (n+1) → 𝕜)
    (i : Fin n) :
    (inverseMatrix b ell).mulVec v i.succ =
      v i.succ - b i * ((1 / 2) * (v 0 + tailPairing ell v)) := by
  simp [inverseMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, tailPairing, ite_mul,
    mul_add, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
  ring

private theorem tailPairing_basis_mulVec (b ell : Fin n → 𝕜)
    (h : ∑ i, ell i * b i = 1) (v : Fin (n+1) → 𝕜) :
    tailPairing ell ((basisMatrix b ell).mulVec v) = v 0 + tailPairing ell v := by
  unfold tailPairing
  simp_rw [basis_mulVec_succ, mul_add, Finset.sum_add_distrib, ← mul_assoc (ell _) (b _),
    ← Finset.sum_mul, h, one_mul]

private theorem two_half_mul (x y : 𝕜) : (1 / 2) * (x - y + (x + y)) = x := by
  ring

theorem inverse_mul_basis (b ell : Fin n → 𝕜) (h : ∑ i, ell i * b i = 1) :
    inverseMatrix b ell * basisMatrix b ell = 1 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  rw [← Matrix.mulVec_mulVec, Matrix.one_mulVec]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [inverse_mulVec_zero, basis_mulVec_zero, tailPairing_basis_mulVec b ell h,
      two_half_mul]
  · rw [inverse_mulVec_succ, basis_mulVec_zero, basis_mulVec_succ,
      tailPairing_basis_mulVec b ell h, two_half_mul]
    ring

def basisUnit (b ell : Fin n → 𝕜) (h : ∑ i, ell i * b i = 1) :
    (Matrix (Fin (n + 1)) (Fin (n + 1)) 𝕜)ˣ :=
  ⟨basisMatrix b ell, inverseMatrix b ell, mul_eq_one_comm.mp (inverse_mul_basis b ell h),
    inverse_mul_basis b ell h⟩

private theorem drift_mulVec (b ell : Fin n → 𝕜) (v : Fin (n+1) → 𝕜)
    (i : Fin (n+1)) :
    (rankOneDrift b ell).mulVec v i =
      Fin.cases 1 b i * ((1 / 2) * (v 0 + tailPairing ell v)) := by
  simp [rankOneDrift, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, tailPairing,
    mul_add, Finset.mul_sum, mul_assoc, mul_left_comm]

private theorem canonical_mulVec_zero (v : Fin (n+1) → 𝕜) :
    (canonicalDrift n).mulVec v 0 = v 0 := by
  simp [canonicalDrift, Matrix.mulVec_diagonal]

private theorem canonical_mulVec_succ (v : Fin (n+1) → 𝕜) (j : Fin n) :
    (canonicalDrift n).mulVec v j.succ = 0 := by
  simp [canonicalDrift, Matrix.mulVec_diagonal]

theorem drift_mul_basis (b ell : Fin n → 𝕜) (h : ∑ i, ell i * b i = 1) :
    rankOneDrift b ell * basisMatrix b ell = basisMatrix b ell * canonicalDrift n := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  funext i
  rw [drift_mulVec, basis_mulVec_zero, tailPairing_basis_mulVec b ell h, two_half_mul]
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [basis_mulVec_zero, canonical_mulVec_zero, tailPairing, canonical_mulVec_succ]
  · simp [basis_mulVec_succ, canonical_mulVec_zero, canonical_mulVec_succ]

theorem conjugate_drift (b ell : Fin n → 𝕜) (h : ∑ i, ell i * b i = 1) :
    inverseMatrix b ell * rankOneDrift b ell * basisMatrix b ell = canonicalDrift n := by
  rw [mul_assoc, drift_mul_basis b ell h, ← mul_assoc, inverse_mul_basis b ell h, one_mul]

end FeedbackCoordinates
end ContinuousBilinear
