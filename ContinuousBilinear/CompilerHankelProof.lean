import ContinuousBilinear.CompilerFiniteSpanProof
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace ContinuousBilinear.PolynomialLift.LinearRepresentation

open Module

variable {𝕜 V ι : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- The Hankel matrix of the output coefficients, with chosen prefix and suffix words. -/
def wordHankel (F : LinearRepresentation 𝕜 V ι) {n : ℕ}
    (u v : Fin n → List ι) : Matrix (Fin n) (Fin n) 𝕜 :=
  Matrix.of fun i j => F.output (F.wordAction (u i ++ v j) F.initial)

private theorem wordHankel_factorization (F : LinearRepresentation 𝕜 V ι)
    {n : ℕ} (b : Basis (Fin n) 𝕜 V) (u v : Fin n → List ι) :
    F.wordHankel u v =
      (Matrix.of (fun i j => F.output (F.wordAction (u i) (b j))) :
        Matrix (Fin n) (Fin n) 𝕜) *
      (Matrix.of (fun i j => b.repr (F.wordAction (v j) F.initial) i) :
        Matrix (Fin n) (Fin n) 𝕜) := by
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply]
  change F.output (F.wordAction (u i ++ v j) F.initial) = _
  rw [wordAction_append]
  let out := F.output.comp (F.wordAction (u i))
  have h := congrArg out (b.sum_repr (F.wordAction (v j) F.initial))
  simp only [map_sum, map_smul, smul_eq_mul] at h
  exact h.symm.trans (Finset.sum_congr rfl (fun k _ => mul_comm _ _))

/-- An invertible selected Hankel matrix certifies independence of both families. -/
theorem det_wordHankel_ne_zero_iff (F : LinearRepresentation 𝕜 V ι)
    {n : ℕ} (b : Basis (Fin n) 𝕜 V) (u v : Fin n → List ι) :
    (F.wordHankel u v).det ≠ 0 ↔
      LinearIndependent 𝕜 (fun i => F.output.comp (F.wordAction (u i))) ∧
      LinearIndependent 𝕜 (fun j => F.wordAction (v j) F.initial) := by
  let R : Matrix (Fin n) (Fin n) 𝕜 := Matrix.of fun i j => F.output (F.wordAction (u i) (b j))
  let C : Matrix (Fin n) (Fin n) 𝕜 := Matrix.of fun i j => b.repr (F.wordAction (v j) F.initial) i
  let r := b.dualBasis.equivFun
  let c := b.equivFun
  have hrmat : R.row = r ∘ (fun i => F.output.comp (F.wordAction (u i))) := by
    funext i j
    exact (b.dualBasis_equivFun (F.output.comp (F.wordAction (u i))) j).symm
  have hcmat : C.col = c ∘ (fun j => F.wordAction (v j) F.initial) := by
    funext i j
    exact (congrFun (b.equivFun_apply (F.wordAction (v i) F.initial)) j).symm
  have hr : LinearIndependent 𝕜 R.row ↔
      LinearIndependent 𝕜 (fun i => F.output.comp (F.wordAction (u i))) := by
    rw [hrmat]
    exact r.toLinearMap.linearIndependent_iff (LinearMap.ker_eq_bot_of_injective r.injective)
  have hc : LinearIndependent 𝕜 C.col ↔
      LinearIndependent 𝕜 (fun j => F.wordAction (v j) F.initial) := by
    rw [hcmat]
    exact c.toLinearMap.linearIndependent_iff (LinearMap.ker_eq_bot_of_injective c.injective)
  calc
    (F.wordHankel u v).det ≠ 0 ↔ R.det * C.det ≠ 0 := by
      have hfact : F.wordHankel u v = R * C := wordHankel_factorization F b u v
      rw [hfact, Matrix.det_mul]
    _ ↔ IsUnit R ∧ IsUnit C := by
      simp only [mul_ne_zero_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    _ ↔ _ := (Matrix.linearIndependent_rows_iff_isUnit.symm.trans hr).and
      (Matrix.linearIndependent_cols_iff_isUnit.symm.trans hc)

/-- Full reachability and observability are equivalent to a nonsingular Hankel
matrix with dimension-many prefix and suffix words of bounded length. -/
theorem minimal_iff_bounded_wordHankel [FiniteDimensional 𝕜 V]
    (F : LinearRepresentation 𝕜 V ι) :
    (F.reachable = ⊤ ∧
      Submodule.span 𝕜 (Set.range fun w : List ι => F.output.comp (F.wordAction w)) = ⊤) ↔
      ∃ u v : Fin (finrank 𝕜 V) → List ι,
        (∀ i, (u i).length ≤ finrank 𝕜 V) ∧
        (∀ j, (v j).length ≤ finrank 𝕜 V) ∧ (F.wordHankel u v).det ≠ 0 := by
  let b := Module.finBasis 𝕜 V
  rw [F.reachable_eq_top_iff_bounded_word_basis, F.rows_span_eq_top_iff_bounded_word_basis]
  constructor
  · rintro ⟨⟨v, hv, hv'⟩, ⟨u, hu, hu'⟩⟩
    exact ⟨u, v, hu, hv, (F.det_wordHankel_ne_zero_iff b u v).mpr ⟨hu', hv'⟩⟩
  · rintro ⟨u, v, hu, hv, hd⟩
    obtain ⟨hu', hv'⟩ := (F.det_wordHankel_ne_zero_iff b u v).mp hd
    exact ⟨⟨v, hv, hv'⟩, ⟨u, hu, hu'⟩⟩

end ContinuousBilinear.PolynomialLift.LinearRepresentation
