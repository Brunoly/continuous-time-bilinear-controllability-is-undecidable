import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

namespace ContinuousBilinear

open Matrix

variable {𝕜 : Type*} [Field 𝕜]

private theorem transvection_pair_rotation {n : Type*} [Fintype n] [DecidableEq n]
    {i j : n} (hij : i ≠ j) {a : 𝕜} (ha : a ≠ 0) :
    transvection i j a * transvection j i (-a⁻¹) * transvection i j a =
      1 - single i i 1 - single j j 1 + single i j a + single j i (-a⁻¹) := by
  simp [transvection, add_mul, mul_add, hij.symm, ha, ← single_neg]
  abel

private theorem diag2n_as_transvections {n : Type*} [Fintype n] [DecidableEq n]
    {i j : n} (hij : i ≠ j) {a : 𝕜} (ha : a ≠ 0) :
    ((Matrix.SpecialLinearGroup.diag2n hij a ha).1 : Matrix n n 𝕜) =
      (transvection i j a * transvection j i (-a⁻¹) * transvection i j a) *
      (transvection i j (-1) * transvection j i 1 * transvection i j (-1)) := by
  rw [transvection_pair_rotation hij ha]
  have hh := transvection_pair_rotation hij (a := (-1 : 𝕜)) (by norm_num)
  simp only [inv_neg, inv_one, neg_neg] at hh
  rw [hh]
  have hExpansion :
      (1 - single i i 1 - single j j 1 + single i j a + single j i (-a⁻¹)) *
        (1 - single i i 1 - single j j 1 + single i j (-1) + single j i 1) =
      (1 - single i i 1 - single j j 1 + single i i a + single j j a⁻¹ : Matrix n n 𝕜) := by
    simp [add_mul, mul_add, sub_mul, mul_sub, hij, hij.symm]
    abel
  rw [hExpansion, Matrix.SpecialLinearGroup.diag2n_coe]
  ext k l
  by_cases hi : k = i <;> by_cases hj : k = j <;>
    simp [Matrix.diagonal_apply, Matrix.one_apply, Matrix.single, hi, hj, eq_comm, hij]
  all_goals split_ifs <;> simp_all

/-- A matrix submonoid containing every elementary transvection contains every
matrix of determinant one. -/
theorem det_one_mem_of_transvections {n : Type*} [Fintype n] [DecidableEq n] [Nontrivial n]
    (S : Submonoid (Matrix n n 𝕜))
    (hS : ∀ i j : n, i ≠ j → ∀ a : 𝕜, transvection i j a ∈ S)
    {A : Matrix n n 𝕜} (hA : det A = 1) : A ∈ S := by
  let P : SpecialLinearGroup n 𝕜 → Prop := fun X => X.1 ∈ S
  change P ⟨A, hA⟩
  apply SpecialLinearGroup.diagonal_transvection_induction' P
  · intro i j hij a ha
    change (SpecialLinearGroup.diag2n hij a ha).1 ∈ S
    rw [diag2n_as_transvections hij ha]
    exact S.mul_mem (S.mul_mem (S.mul_mem (hS i j hij _) (hS j i hij.symm _)) (hS i j hij _))
      (S.mul_mem (S.mul_mem (hS i j hij _) (hS j i hij.symm _)) (hS i j hij _))
  · intro i j hij a
    exact hS i j hij a
  · intro X Y hX hY
    exact S.mul_mem hX hY

end ContinuousBilinear
