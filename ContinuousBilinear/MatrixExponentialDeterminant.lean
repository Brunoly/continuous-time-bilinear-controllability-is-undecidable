import ContinuousBilinear.Definitions
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.LinearAlgebra.Matrix.Trace

open scoped Matrix.Norms.Operator

namespace ContinuousBilinear

private theorem exists_ne_fixed_of_perm_ne_one {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (hσ : σ ≠ 1) (i : Fin n) : ∃ j, j ≠ i ∧ σ j ≠ j := by
  by_contra! h
  apply hσ
  apply Equiv.ext
  intro j
  change σ j = j
  by_cases hj : j = i
  · subst j
    by_contra hi
    exact hi (σ.injective (h (σ i) hi))
  · exact h j hj

private theorem hasDerivAt_det_of_eq_one {n : ℕ}
    {f : ℝ → RealMatrix n} {t : ℝ} {B : RealMatrix n}
    (h₁ : f t = 1) (hf : HasDerivAt f B t) :
    HasDerivAt (fun s => (f s).det) B.trace t := by
  classical
  let sign (σ : Equiv.Perm (Fin n)) : ℝ := (Equiv.Perm.sign σ : ℤ)
  let term (σ : Equiv.Perm (Fin n)) (s : ℝ) := ∏ i : Fin n, f s (σ i) i
  let coefficient (σ : Equiv.Perm (Fin n)) :=
    ∑ i : Fin n, (∏ j ∈ Finset.univ.erase i, f t (σ j) j) * B (σ i) i
  have hEntry (i j : Fin n) : HasDerivAt (fun s => f s i j) (B i j) t := by
    let eval : RealMatrix n →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
      { toFun := fun M => M i j
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact eval.hasFDerivAt.comp_hasDerivAt t hf
  have hTerm (σ : Equiv.Perm (Fin n)) : HasDerivAt (term σ) (coefficient σ) t := by
    exact HasDerivAt.fun_finsetProd (fun i _ => hEntry (σ i) i)
  have hSum := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Equiv.Perm (Fin n))))
    (fun σ _ => (hTerm σ).const_mul (sign σ))
  have hcoef : ∑ σ : Equiv.Perm (Fin n), sign σ * coefficient σ = B.trace := by
    rw [Finset.sum_eq_single 1]
    · simp [sign, coefficient, h₁, Matrix.trace, Matrix.one_apply]
    · intro σ _ hσ
      have hz : coefficient σ = 0 := by
        unfold coefficient
        apply Finset.sum_eq_zero
        intro i _
        obtain ⟨j, hji, hj⟩ := exists_ne_fixed_of_perm_ne_one hσ i
        have hzero : (∏ k ∈ Finset.univ.erase i, f t (σ k) k) = 0 := by
          apply Finset.prod_eq_zero (i := j)
          · exact Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩
          · rw [h₁, Matrix.one_apply_ne hj]
        rw [hzero, zero_mul]
      rw [hz, mul_zero]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  rw [hcoef] at hSum
  exact hSum.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun s => Matrix.det_apply' (f s)))

private theorem det_exp_smul_add {n : ℕ} (M : RealMatrix n) (t s : ℝ) :
    (NormedSpace.exp ((t + s) • M)).det =
      (NormedSpace.exp (t • M)).det * (NormedSpace.exp (s • M)).det := by
  have h : Commute (t • M) (s • M) := ((Commute.refl M).smul_left t).smul_right s
  rw [add_smul, Matrix.exp_add_of_commute _ _ h, Matrix.det_mul]

private theorem hasDerivAt_det_exp_smul {n : ℕ} (M : RealMatrix n) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (NormedSpace.exp (s • M)).det)
      ((NormedSpace.exp (t • M)).det * M.trace) t := by
  let f (s : ℝ) := (NormedSpace.exp (s • M)).det
  have h₀ : HasDerivAt f M.trace 0 := by
    apply hasDerivAt_det_of_eq_one
    · simp
    · have hd := hasDerivAt_exp_smul_const M (0 : ℝ)
      rw [zero_smul, NormedSpace.exp_zero, one_mul] at hd
      exact hd
  have hs : HasDerivAt (fun s : ℝ => s - t) 1 t := (hasDerivAt_id t).sub_const t
  have hShift : HasDerivAt (fun s : ℝ => f (s - t)) M.trace t := by
    simpa only [Function.comp_def, mul_one] using h₀.comp_of_eq t hs (sub_self t).symm
  refine (hShift.const_mul (f t)).congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro s
  change f s = f t * f (s - t)
  rw [← det_exp_smul_add M t (s-t), show t + (s - t) = s by ring]

/-- The determinant of a real matrix exponential is the scalar exponential of its trace. -/
theorem det_exp_smul {n : ℕ} (M : RealMatrix n) (t : ℝ) :
    (NormedSpace.exp (t • M)).det = Real.exp (t * M.trace) := by
  let f (s : ℝ) := (NormedSpace.exp (s • M)).det
  let w (s : ℝ) := Real.exp (-(s * M.trace)) * f s
  have hw (s : ℝ) : HasDerivAt w 0 s := by
    have hReal : HasDerivAt (fun r : ℝ => Real.exp (-(r * M.trace)))
        (Real.exp (-(s * M.trace)) * (-M.trace)) s :=
      ((hasDerivAt_id s).mul_const M.trace).neg.exp.congr_deriv (by simp)
    have hh := hReal.mul (hasDerivAt_det_exp_smul M s)
    exact hh.congr_deriv (by ring)
  have hc : w t = w 0 :=
    is_const_of_deriv_eq_zero (fun s => (hw s).differentiableAt) (fun s => (hw s).deriv) t 0
  have hOne : w 0 = 1 := by simp [w, f]
  have he : Real.exp (-(t * M.trace)) * f t = 1 := hc.trans hOne
  have he' := congrArg (Real.exp (t * M.trace) * ·) he
  rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul, mul_one] at he'
  exact he'

end ContinuousBilinear
