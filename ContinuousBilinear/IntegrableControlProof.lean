import ContinuousBilinear.ODEProof
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.MeasureTheory.Function.LocallyIntegrable

namespace ContinuousBilinear

open Set MeasureTheory
open scoped Interval

private theorem intervalIntegrable_iff_Icc {E : Type*} [NormedAddCommGroup E]
    {f : ℝ → E} {a b : ℝ} (hab : a ≤ b) :
    IntervalIntegrable f volume a b ↔ IntegrableOn f (Icc a b) :=
  intervalIntegrable_iff_integrableOn_Icc_of_le hab (by finiteness)

/-- Products of integrable matrix coefficients and continuous states are integrable
on each compact time interval. -/
theorem integrableOn_generator_mulVec (P : Plant ℝ) {u : ℝ → Fin P.controls → ℝ}
    {z : ℝ → State P.dimension} {a b : ℝ}
    (hu : IntegrableOn u (Icc a b)) (hz : ContinuousOn z (Icc a b)) :
    IntegrableOn (fun t => (generator P (u t)).mulVec (z t)) (Icc a b) := by
  apply Integrable.of_eval
  intro i
  unfold Matrix.mulVec dotProduct
  apply integrable_finsetSum
  intro j _
  have hcoef : IntegrableOn (fun t => generator P (u t) i j) (Icc a b) := by
    simp only [generator, Matrix.add_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    apply Integrable.add
    · exact integrableOn_const isCompact_Icc.measure_lt_top.ne
    · apply integrable_finsetSum
      intro k _
      exact (hu.eval k).mul_const _
  exact hcoef.mul_continuousOn ((continuous_apply j).comp_continuousOn hz) isCompact_Icc

/-- Constant controls are admissible for the finite-horizon integral equation. -/
theorem integrableControlReachable_of_constantControlSegment (P : Plant ℝ)
    {x y : State P.dimension} (h : ConstantControlSegment P x y) :
    IntegrableControlReachable P x y := by
  obtain ⟨T, u, z, hT, h0, hEnd, hDeriv⟩ := h
  have hz : ContinuousOn z (Icc 0 T) :=
    fun t ht => (hDeriv t ht).continuousWithinAt
  have hu : IntegrableOn (fun _ : ℝ => u) (Icc 0 T) :=
    integrableOn_const isCompact_Icc.measure_lt_top.ne
  refine ⟨T, fun _ => u, z, hT.le, hu, hz, h0, hEnd, ?_⟩
  intro t ht
  have hst : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have hi := (intervalIntegrable_iff_Icc ht.1).mpr
    (integrableOn_generator_mulVec P (hu.mono_set hst) (hz.mono hst))
  have hFund := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.1 (hz.mono hst)
    (fun r hr => ((hDeriv r ⟨hr.1.le, hr.2.le.trans ht.2⟩).hasDerivAt
      (Icc_mem_nhds hr.1 (hr.2.trans_le ht.2))).hasDerivWithinAt) hi
  rw [hFund, h0]
  abel

theorem IntegrableControlReachable.refl (P : Plant ℝ) (x : State P.dimension) :
    IntegrableControlReachable P x x := by
  refine ⟨0, fun _ => 0, fun _ => x, le_rfl,
    integrableOn_const isCompact_Icc.measure_lt_top.ne, continuousOn_const,
    rfl, rfl, ?_⟩
  intro t ht
  have ht' : t = 0 := le_antisymm ht.2 ht.1
  simp [ht']

/-- Concatenation preserves the integral equation, with the second control shifted
by the duration of the first. -/
theorem IntegrableControlReachable.trans {P : Plant ℝ} {x y z : State P.dimension}
    (hxy : IntegrableControlReachable P x y) (hyz : IntegrableControlReachable P y z) :
    IntegrableControlReachable P x z := by
  classical
  obtain ⟨T, u₁, f₁, hT, hu₁, hf₁, hf₁0, hf₁T, hInt₁⟩ := hxy
  obtain ⟨U, u₂, f₂, hU, hu₂, hf₂, hf₂0, hf₂U, hInt₂⟩ := hyz
  let u (t : ℝ) := if t ≤ T then u₁ t else u₂ (t - T)
  let f (t : ℝ) := if t ≤ T then f₁ t else f₂ (t - T)
  have hTU : T ≤ T + U := le_add_of_nonneg_right hU
  have hfirst : EqOn f f₁ (Icc 0 T) := by
    intro t ht
    simp [f, ht.2]
  have hsecond : EqOn f (fun t => f₂ (t - T)) (Icc T (T + U)) := by
    intro t ht
    rcases lt_or_eq_of_le ht.1 with h | h
    · simp [f, h.not_ge]
    · subst t
      simp [f, hf₁T, hf₂0]
  have hf : ContinuousOn f (Icc 0 (T + U)) := by
    have h₁ : ContinuousOn f (Icc 0 T) := hf₁.congr hfirst
    have h₂ : ContinuousOn f (Icc T (T + U)) := by
      apply (hf₂.comp (continuous_id.sub continuous_const).continuousOn ?_).congr hsecond
      intro t ht
      change t - T ∈ Icc 0 U
      exact ⟨sub_nonneg.mpr ht.1, sub_le_iff_le_add.mpr (by linarith [ht.2])⟩
    rw [← Icc_union_Icc_eq_Icc hT hTU]
    exact h₁.union_of_isClosed h₂ isClosed_Icc isClosed_Icc
  have hu : IntegrableOn u (Icc 0 (T + U)) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc, ← Ioc_union_Ioc_eq_Ioc hT hTU]
    apply IntegrableOn.union
    · exact (hu₁.mono_set Ioc_subset_Icc_self).congr_fun
        (fun t ht => by simp [u, ht.2]) measurableSet_Ioc
    · have hShift : IntervalIntegrable (fun t : ℝ => u₂ (t - T)) volume T (T + U) := by
        simpa [add_comm] using ((intervalIntegrable_iff_Icc hU).mpr hu₂).comp_sub_right T
      exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le hTU).mp hShift).congr_fun
        (fun t ht => by simp [u, ht.1.not_ge]) measurableSet_Ioc
  refine ⟨T + U, u, f, add_nonneg hT hU, hu, hf,
    (hfirst ⟨le_rfl, hT⟩).trans hf₁0, ?_, ?_⟩
  · simpa using (hsecond ⟨hTU, le_rfl⟩).trans (by simpa using hf₂U)
  intro t ht
  let g (s : ℝ) := (generator P (u s)).mulVec (f s)
  let g₁ (s : ℝ) := (generator P (u₁ s)).mulVec (f₁ s)
  let g₂ (s : ℝ) := (generator P (u₂ s)).mulVec (f₂ s)
  have heq₁ (b : ℝ) (hb : b ∈ Icc 0 T) :
      (∫ s in (0 : ℝ)..b, g s) = ∫ s in (0 : ℝ)..b, g₁ s := by
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le hb.1]
    intro s hs
    have hsT := hs.2.trans hb.2
    simp [g, g₁, u, f, hsT]
  by_cases h : t ≤ T
  · rw [heq₁ t ⟨ht.1, h⟩, hfirst ⟨ht.1, h⟩]
    exact hInt₁ t ⟨ht.1, h⟩
  · have htT : T ≤ t := le_of_not_ge h
    have hg : IntegrableOn g (Icc 0 (T + U)) := integrableOn_generator_mulVec P hu hf
    have hg₁ : IntervalIntegrable g volume 0 T :=
      (intervalIntegrable_iff_Icc hT).mpr (hg.mono_set (Icc_subset_Icc_right hTU))
    have hg₂ : IntervalIntegrable g volume T t :=
      (intervalIntegrable_iff_Icc htT).mpr (hg.mono_set (Icc_subset_Icc hT ht.2))
    have heq₂ : (∫ s in T..t, g s) = ∫ s in (0 : ℝ)..t - T, g₂ s := by
      calc
        _ = ∫ s in T..t, g₂ (s - T) := by
          apply intervalIntegral.integral_congr_Ioo_of_le htT
          intro s hs
          simp [g, g₂, u, f, hs.1.not_ge]
        _ = _ := by rw [intervalIntegral.integral_comp_sub_right, sub_self]
    have hft : f t = f₂ (t - T) := by simp [f, h]
    rw [← intervalIntegral.integral_add_adjacent_intervals hg₁ hg₂, heq₁ T ⟨hT, le_rfl⟩,
      heq₂, hft, ← add_assoc]
    have hy : y = x + ∫ s in (0 : ℝ)..T, g₁ s := hf₁T ▸ hInt₁ T ⟨hT, le_rfl⟩
    rw [← hy]
    exact hInt₂ (t - T) ⟨sub_nonneg.mpr htT, by linarith [ht.2]⟩

/-- A reachability witness with finitely many constant-control intervals is also
a witness for the finite-horizon integral equation. -/
theorem integrableControlReachable_of_piecewiseConstantReachable (P : Plant ℝ)
    {x y : State P.dimension} (h : PiecewiseConstantReachable P x y) :
    IntegrableControlReachable P x y := by
  induction h with
  | refl => exact IntegrableControlReachable.refl P _
  | tail _ hStep ih =>
    exact ih.trans (integrableControlReachable_of_constantControlSegment P hStep)

theorem integrableControlReachable_of_transition (P : Plant ℝ) {M : RealMatrix P.dimension}
    (hM : M ∈ transitionMonoid P) (x : State P.dimension) :
    IntegrableControlReachable P x (M.mulVec x) :=
  integrableControlReachable_of_piecewiseConstantReachable P
    ((differentialEquationSemantics P x _).mpr ⟨M, hM, rfl⟩)

theorem GloballyControllable.integrableControls {P : Plant ℝ} (h : GloballyControllable P) :
    GloballyControllableWithIntegrableControls P := by
  intro x y hx hy
  obtain ⟨M, hM, rfl⟩ := h x y hx hy
  exact integrableControlReachable_of_transition P hM x

/-- A finite-horizon integrable control can be extended by zero to a locally
integrable control on the nonnegative time axis, with the same trajectory
on the original horizon. -/
theorem integrableControlReachable_iff_locallyIntegrableOn (P : Plant ℝ)
    (x y : State P.dimension) :
    IntegrableControlReachable P x y ↔
      ∃ (T : ℝ) (u : ℝ → Fin P.controls → ℝ) (z : ℝ → State P.dimension),
        0 ≤ T ∧ LocallyIntegrableOn u (Ici 0) ∧
        ContinuousOn z (Icc 0 T) ∧ z 0 = x ∧ z T = y ∧
        ∀ t ∈ Icc 0 T,
          z t = x + ∫ s in (0 : ℝ)..t, (generator P (u s)).mulVec (z s) := by
  constructor
  · rintro ⟨T, u, z, hT, hu, hz, h0, hEnd, hEq⟩
    let v := (Icc 0 T).indicator u
    have hv : LocallyIntegrableOn v (Ici 0) :=
      (hu.integrable_indicator measurableSet_Icc).locallyIntegrable.locallyIntegrableOn _
    refine ⟨T, v, z, hT, hv, hz, h0, hEnd, fun t ht => ?_⟩
    rw [hEq t ht]
    congr 1
    exact intervalIntegral.integral_congr fun s hs => by
      have hs' : s ∈ Icc 0 t := by simpa only [uIcc_of_le ht.1] using hs
      simp only [v, indicator_of_mem (Icc_subset_Icc_right ht.2 hs')]
  · rintro ⟨T, u, z, hT, hu, hz, h0, hEnd, hEq⟩
    refine ⟨T, u, z, hT, ?_, hz, h0, hEnd, hEq⟩
    exact hu.integrableOn_compact_subset (fun _ hs => hs.1) isCompact_Icc

end ContinuousBilinear
