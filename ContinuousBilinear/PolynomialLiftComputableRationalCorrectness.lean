import ContinuousBilinear.PolynomialLiftComputableCorrectness
import ContinuousBilinear.PolynomialLiftComputableRational
import ContinuousBilinear.PolynomialLiftQuotientDynamics

namespace ContinuousBilinear
namespace PolynomialLift

open scoped BigOperators Matrix Matrix.Norms.Operator

/-- The exact normalized scalar coefficient of the rational tables supplied to a reduction. -/
theorem compileRationalLift_matrix_coefficient (p : IntegerPolynomialCode) (u : SignChannel p → ℝ) :
    let c := compileRationalLift p
    (∑ j, (c.output j : ℝ) *
      ((NormedSpace.exp (realPencil c.operator (u ∘ compiledRationalChannelEquiv p))).mulVec
        (fun j => (c.initial j : ℝ))) j) =
      p.signPolynomialValue (fun i => u (some i)) (fun i => Real.sin (u (some i))) (u none) /
        ((signBaseValue p) : ℝ) := by
  let c := compileRationalLift p
  let e := finCongr (compileRationalLift_channelCount p)
  have hgen : realPencil c.operator (u ∘ compiledRationalChannelEquiv p) =
      (∑ k : Fin (p.arity + 2), u (oscillatorChannelAt (p.arity + 1) k) •
        (compiledSignMatrices p k).map (Int.castRingHom ℝ) :
        RealMatrix (compilePolynomialLift p).1) := by
    unfold realPencil
    refine Fintype.sum_equiv e _ _ (fun k => ?_)
    apply congrArg₂ (· • ·)
    · rfl
    · ext i j
      simp only [Matrix.map_apply, c, compileRationalLift_operator, Rat.coe_castHom,
        Rat.cast_intCast, Int.coe_castRingHom, e]
      rfl
  have hb : (fun j => (c.initial j : ℝ)) = fun j => (compiledSignInitial p j : ℝ) := by
    funext j
    simp only [c, compileRationalLift_initial, Rat.cast_intCast]
  change (∑ j, (c.output j : ℝ) *
    ((NormedSpace.exp (realPencil c.operator (u ∘ compiledRationalChannelEquiv p))).mulVec
      (fun j => (c.initial j : ℝ))) j) = _
  rw [hgen, hb, ← compiledSign_matrix_coefficient p u]
  refine Finset.sum_congr (rfl : (Finset.univ : Finset (Fin c.1)) = Finset.univ) (fun j _ => ?_)
  let G : RealMatrix (compilePolynomialLift p).1 :=
    ∑ k : Fin (p.arity + 2), u (oscillatorChannelAt (p.arity + 1) k) •
      (compiledSignMatrices p k).map (Int.castRingHom ℝ)
  exact congrArg (fun a : ℚ => (a : ℝ) *
    ((NormedSpace.exp G).mulVec (fun k => (compiledSignInitial p k : ℝ))) j)
    (compileRationalLift_output p j)

theorem compileRationalLift_initial_coefficient (p : IntegerPolynomialCode) :
    let c := compileRationalLift p
    (∑ j, c.output j * c.initial j) = 1 := by
  let c := compileRationalLift p
  change (∑ j, c.output j * c.initial j) = 1
  have h : (∑ j, c.output j * c.initial j) =
      ∑ j, signOutputRow p j * (signInitialVector p j : ℚ) := by
    let e : Fin c.1 ≃ Fin (signDimension p) := liftIndexEquiv p
    refine Fintype.sum_equiv e _ _ (fun j => ?_)
    exact congrArg₂ (· * ·) ((compileRationalLift_output p j).trans (compiledSignOutput_entry p j))
      ((compileRationalLift_initial p j).trans
        (congrArg (Int.cast : ℤ → ℚ) (compiledSignInitial_entry p j)))
  rw [h]
  exact_mod_cast signOutput_initial p

/-- A negative exponential coefficient of the computably produced rational representation
exists exactly when the polynomial has an integer zero. -/
theorem compileRationalLift_negative_iff (p : IntegerPolynomialCode) :
    let c := compileRationalLift p
    (∃ v : Fin c.2.2.2.length → ℝ,
      (∑ j, (c.output j : ℝ) *
        ((NormedSpace.exp (realPencil c.operator v)).mulVec (fun j => (c.initial j : ℝ))) j) < 0) ↔
      p.HasIntegerRoot := by
  let c := compileRationalLift p
  let e := compiledRationalChannelEquiv p
  have hpos : (0 : ℝ) < signBaseValue p := by exact_mod_cast signBaseValue_pos p
  constructor
  · rintro ⟨v, hv⟩
    let u : SignChannel p → ℝ := v ∘ e.symm
    have hu : u ∘ e = v := by
      funext k
      simp [u, Function.comp_def]
    have hh := compileRationalLift_matrix_coefficient p u
    change (∑ j, (c.output j : ℝ) *
      ((NormedSpace.exp (realPencil c.operator (u ∘ e))).mulVec (fun j => (c.initial j : ℝ))) j) = _ at hh
    rw [hu] at hh
    rw [hh] at hv
    exact p.hasIntegerRoot_of_negative (fun i => u (some i)) (u none)
      (by simpa only [zero_mul] using (div_lt_iff₀ hpos).mp hv)
  · intro hp
    obtain ⟨q, a, ha⟩ := p.exists_negative_of_hasIntegerRoot hp
    let u : SignChannel p → ℝ := fun i => i.elim a q
    refine ⟨u ∘ e, ?_⟩
    rw [compileRationalLift_matrix_coefficient p u]
    apply (div_lt_iff₀ hpos).mpr
    simpa only [u, zero_mul, Option.elim_some, Option.elim_none] using ha

end PolynomialLift
end ContinuousBilinear
