import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Set.Function

namespace ContinuousBilinear

/-- A vanishing residual outside the selected rows and columns gives a factorization
of every entry through the inverse of the selected block. -/
theorem entry_eq_selectedBlock_factorization
    {α β : Type*} {n : ℕ} (M : α → β → ℚ) (u : Fin n → α) (v : Fin n → β)
    (R : Matrix (Fin n) (Fin n) ℚ)
    (hHR : (Matrix.of (fun i j => M (u i) (v j))) * R = 1)
    (hRH : R * (Matrix.of (fun i j => M (u i) (v j))) = 1)
    (hrest : ∀ a ∉ Set.range u, ∀ b ∉ Set.range v,
      M a b = ∑ j, M a (v j) * (R.mulVec (fun i => M (u i) b)) j) :
    ∀ a b, M a b = ∑ j, M a (v j) * (R.mulVec (fun i => M (u i) b)) j := by
  classical
  let H : Matrix (Fin n) (Fin n) ℚ := Matrix.of fun i j => M (u i) (v j)
  change H * R = 1 at hHR
  change R * H = 1 at hRH
  intro a b
  by_cases ha : a ∈ Set.range u
  · obtain ⟨i, rfl⟩ := ha
    let x : Fin n → ℚ := fun k => M (u k) b
    have h : H.mulVec (R.mulVec x) = x := by
      rw [Matrix.mulVec_mulVec, hHR, Matrix.one_mulVec]
    exact (congrFun h i).symm
  · by_cases hb : b ∈ Set.range v
    · obtain ⟨j, rfl⟩ := hb
      let e : Fin n → ℚ := Pi.single j 1
      have he : H.mulVec e = fun i => M (u i) (v j) := by
        rw [show e = Pi.single j 1 from rfl, Matrix.mulVec_single_one]
        rfl
      have h : R.mulVec (fun i => M (u i) (v j)) = e := by
        rw [← he, Matrix.mulVec_mulVec, hRH, Matrix.one_mulVec]
      rw [h]
      exact (dotProduct_single_one (fun k => M a (v k)) j).symm
    · exact hrest a ha b hb

end ContinuousBilinear
