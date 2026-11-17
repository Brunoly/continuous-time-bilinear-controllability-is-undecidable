import ContinuousBilinear.PolynomialLiftQuotientCoordinates
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

namespace ContinuousBilinear
namespace PolynomialLift

open scoped BigOperators Matrix
open Filter

noncomputable section

/-- The span of the exponential orbit of a commuting matrix family. -/
def exponentialOrbitSpan {ι : Type*} [Fintype ι] {n : ℕ}
    (K : ι → RealMatrix n) (x : State n) : Submodule ℝ (State n) :=
  Submodule.span ℝ (Set.range fun u : ι → ℝ =>
    (NormedSpace.exp (∑ i, u i • K i)).mulVec x)

theorem mem_exponentialOrbitSpan {ι : Type*} [Fintype ι] {n : ℕ}
    (K : ι → RealMatrix n) (x : State n) : x ∈ exponentialOrbitSpan K x := by
  apply Submodule.subset_span
  refine ⟨fun _ => 0, ?_⟩
  simp [NormedSpace.exp_zero]

theorem exponentialOrbitSpan_exp_invariant {ι : Type*} [Fintype ι] {n : ℕ}
    (K : ι → RealMatrix n) (hK : ∀ i j, Commute (K i) (K j))
    (x : State n) (i : ι) (t : ℝ) (y : State n) (hy : y ∈ exponentialOrbitSpan K x) :
    (NormedSpace.exp (t • K i)).mulVec y ∈ exponentialOrbitSpan K x := by
  classical
  let A := NormedSpace.exp (t • K i)
  change A.mulVec y ∈ exponentialOrbitSpan K x
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, rfl⟩ := hy
    dsimp only [A]
    rw [Matrix.mulVec_mulVec, ← Matrix.exp_add_of_commute _ _]
    · apply Submodule.subset_span
      refine ⟨fun j => u j + if j = i then t else 0, ?_⟩
      have hsum : (∑ j, (u j + if j = i then t else 0) • K j) =
          t • K i + ∑ j, u j • K j := by
        simp only [add_smul, Finset.sum_add_distrib]
        simp_rw [ite_smul, zero_smul]
        simp [add_comm]
      dsimp only
      rw [hsum]
    · refine Commute.sum_right Finset.univ _ _ (fun j _ => ?_)
      change (t • K i) * (u j • K j) = (u j • K j) * (t • K i)
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, (hK i j).eq]
      rw [smul_comm]
  | zero => simp
  | add a b ha hb h₁ h₂ =>
    rw [Matrix.mulVec_add]
    exact (exponentialOrbitSpan K x).add_mem h₁ h₂
  | smul c a ha ih =>
    rw [Matrix.mulVec_smul]
    exact (exponentialOrbitSpan K x).smul_mem c ih

/-- Differentiating the exponential action at zero gives invariance under the generators. -/
theorem exponentialOrbitSpan_invariant {ι : Type*} [Fintype ι] {n : ℕ}
    (K : ι → RealMatrix n) (hK : ∀ i j, Commute (K i) (K j))
    (x : State n) (i : ι) (y : State n) (hy : y ∈ exponentialOrbitSpan K x) :
    (K i).mulVec y ∈ exponentialOrbitSpan K x := by
  let f : ℝ → State n := fun t => (NormedSpace.exp (t • K i)).mulVec y
  have hder : HasDerivAt f ((K i).mulVec y) 0 := by
    simpa only [zero_smul, NormedSpace.exp_zero, Matrix.one_mulVec] using
      hasDerivAt_exp_mulVec (K i) y 0
  refine (exponentialOrbitSpan K x).closed_of_finiteDimensional.mem_of_tendsto
    hder.tendsto_slope (Eventually.of_forall fun t => ?_)
  rw [slope_def_module]
  apply Submodule.smul_mem
  exact (exponentialOrbitSpan K x).sub_mem
    (exponentialOrbitSpan_exp_invariant K hK x i t y hy)
    (exponentialOrbitSpan_exp_invariant K hK x i 0 y hy)

/-- The closed finite-dimensional orbit span contains every generator word applied to the base. -/
theorem word_mem_exponentialOrbitSpan {ι : Type*} [Fintype ι] {n : ℕ}
    (K : ι → RealMatrix n) (hK : ∀ i j, Commute (K i) (K j))
    (x : State n) (w : List ι) :
    w.foldr (fun i y => (K i).mulVec y) x ∈ exponentialOrbitSpan K x := by
  induction w with
  | nil => exact mem_exponentialOrbitSpan K x
  | cons i w ih => exact exponentialOrbitSpan_invariant K hK x i _ ih

namespace LinearRepresentation

open Module

variable {V ι : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι] {n : ℕ}

def realOperators (F : LinearRepresentation ℚ V ι) (b : Basis (Fin n) ℚ V)
    (i : ι) : RealMatrix n :=
  (F.coordinateOperators b i).map (Rat.castHom ℝ)

def realRow (b : Basis (Fin n) ℚ V) (φ : V →ₗ[ℚ] ℚ) : State n :=
  fun j => (φ (b j) : ℝ)

omit [Fintype ι] in
theorem realOperators_commute (F : LinearRepresentation ℚ V ι) (b : Basis (Fin n) ℚ V)
    (h : ∀ i j, Commute (F.operator i) (F.operator j)) (i j : ι) :
    Commute (F.realOperators b i) (F.realOperators b j) := by
  change _ * _ = _ * _
  unfold realOperators coordinateOperators
  simp only [← Matrix.map_mul, ← LinearMap.toMatrix_mul, (h i j).eq]

private theorem basis_mem_top_of_standard (S : Submodule ℝ (State n))
    (h : ∀ j : Fin n, Pi.single j (1 : ℝ) ∈ S) : S = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  have he := (Pi.basisFun ℝ (Fin n)).sum_repr x
  rw [← he]
  exact S.sum_mem (fun j _ => S.smul_mem _ (by simpa only [Pi.basisFun_apply] using h j))

theorem exponential_columns_span (F : LinearRepresentation ℚ V ι) (b : Basis (Fin n) ℚ V)
    (hcomm : ∀ i j, Commute (F.operator i) (F.operator j)) (hgen : F.reachable = ⊤) :
    exponentialOrbitSpan (F.realOperators b) (realCoordinates b F.initial) = ⊤ := by
  let S := exponentialOrbitSpan (F.realOperators b) (realCoordinates b F.initial)
  have hcoord (x : V) (hx : x ∈ F.reachable) : realCoordinates b x ∈ S := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      induction w with
      | nil => exact mem_exponentialOrbitSpan _ _
      | cons i w ih =>
        change realCoordinates b (F.wordAction (i :: w) F.initial) ∈ S
        rw [wordAction_cons, ← realCoordinates_map (F.operator i) b b]
        exact exponentialOrbitSpan_invariant _ (F.realOperators_commute b hcomm) _ _ _ ih
    | zero =>
      have he : realCoordinates b 0 = 0 := by funext j; simp [realCoordinates]
      rw [he]
      exact S.zero_mem
    | add x y hx hy h₁ h₂ =>
      have he : realCoordinates b (x + y) = realCoordinates b x + realCoordinates b y := by
        funext j
        simp [realCoordinates]
      rw [he]
      exact S.add_mem h₁ h₂
    | smul c x hx ih =>
      have hcast : realCoordinates b (c • x) = (c : ℝ) • realCoordinates b x := by
        funext j
        simp [realCoordinates, smul_eq_mul]
      rw [hcast]
      exact S.smul_mem _ ih
  apply basis_mem_top_of_standard
  intro j
  have hj := hcoord (b j) (by rw [hgen]; trivial)
  have he : realCoordinates b (b j) = Pi.single j 1 := by
    funext k
    by_cases h : j = k <;> simp [realCoordinates, Finsupp.single_apply, Pi.single_apply, h, eq_comm]
  exact he ▸ hj

omit [Fintype ι] in
private theorem realRow_comp (F : LinearRepresentation ℚ V ι) (b : Basis (Fin n) ℚ V)
    (φ : V →ₗ[ℚ] ℚ) (i : ι) :
    (F.realOperators b i).transpose.mulVec (realRow b φ) =
      realRow b (φ.comp (F.operator i)) := by
  funext j
  have h := congrArg φ (b.sum_repr (F.operator i (b j)))
  simp only [map_sum, map_smul, smul_eq_mul] at h
  have h' := congrArg (Rat.castHom ℝ) h
  simpa only [realOperators, coordinateOperators, realRow, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, Matrix.map_apply, LinearMap.toMatrix_apply,
    LinearMap.comp_apply, Rat.coe_castHom, map_sum, map_mul] using h'

theorem exponential_rows_transpose_span (F : LinearRepresentation ℚ V ι)
    (b : Basis (Fin n) ℚ V) (hcomm : ∀ i j, Commute (F.operator i) (F.operator j))
    (hobs : Submodule.span ℚ (Set.range fun w : List ι => F.output.comp (F.wordAction w)) = ⊤) :
    exponentialOrbitSpan (fun i => (F.realOperators b i).transpose) (realRow b F.output) = ⊤ := by
  let K := fun i => (F.realOperators b i).transpose
  let S := exponentialOrbitSpan K (realRow b F.output)
  have hK (i j : ι) : Commute (K i) (K j) := by
    change _ * _ = _ * _
    dsimp only [K]
    simp only [← Matrix.transpose_mul, (F.realOperators_commute b hcomm j i).eq]
  have hword (w : List ι) (φ : V →ₗ[ℚ] ℚ) (hφ : realRow b φ ∈ S) :
      realRow b (φ.comp (F.wordAction w)) ∈ S := by
    induction w generalizing φ with
    | nil => exact hφ
    | cons i w ih =>
      have he : φ.comp (F.wordAction (i :: w)) =
        (φ.comp (F.operator i)).comp (F.wordAction w) := rfl
      rw [he]
      apply ih
      rw [← realRow_comp]
      exact exponentialOrbitSpan_invariant K hK _ _ _ hφ
  have hcoord (φ : V →ₗ[ℚ] ℚ)
      (hφ : φ ∈ Submodule.span ℚ (Set.range fun w : List ι => F.output.comp (F.wordAction w))) :
      realRow b φ ∈ S := by
    induction hφ using Submodule.span_induction with
    | mem φ hφ =>
      obtain ⟨w, rfl⟩ := hφ
      exact hword w _ (mem_exponentialOrbitSpan _ _)
    | zero =>
      have he : realRow b 0 = 0 := by funext j; simp [realRow]
      rw [he]
      exact S.zero_mem
    | add φ ψ hφ hψ h₁ h₂ =>
      have he : realRow b (φ + ψ) = realRow b φ + realRow b ψ := by
        funext j
        simp [realRow]
      rw [he]
      exact S.add_mem h₁ h₂
    | smul c φ hφ ih =>
      have he : realRow b (c • φ) = (c : ℝ) • realRow b φ := by
        funext j
        simp [realRow, smul_eq_mul]
      rw [he]
      exact S.smul_mem _ ih
  apply basis_mem_top_of_standard
  intro j
  have hj := hcoord (b.coord j) (by rw [hobs]; trivial)
  have he : realRow b (b.coord j) = Pi.single j 1 := by
    funext k
    by_cases h : j = k <;> simp [realRow, Basis.coord_apply, Finsupp.single_apply, Pi.single_apply, h, eq_comm]
  exact he ▸ hj

end LinearRepresentation

end
end PolynomialLift
end ContinuousBilinear
