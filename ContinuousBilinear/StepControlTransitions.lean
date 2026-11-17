import ContinuousBilinear.IntegrableControlProof
import Mathlib.Topology.Order.ProjIcc

namespace ContinuousBilinear

open Set MeasureTheory
open scoped Interval

/-- On a constant-control interval, an integral-equation trajectory is the
matrix-exponential solution. The control at the right endpoint is immaterial. -/
theorem segmentTransition_eq_of_integral_of_eqOn (P : Plant ℝ)
    {T a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    {u : ℝ → Fin P.controls → ℝ} {z : ℝ → State P.dimension}
    (v : Fin P.controls → ℝ) (hstep : EqOn u (fun _ => v) (Ico a b))
    (hu : IntegrableOn u (Icc 0 T)) (hz : ContinuousOn z (Icc 0 T))
    (hInt : ∀ t ∈ Icc 0 T, z t = z 0 + ∫ s in 0..t,
      (generator P (u s)).mulVec (z s)) :
    (segmentTransition P (b - a) v).mulVec (z a) = z b := by
  let integrand (s : ℝ) := (generator P (u s)).mulVec (z s)
  have hi : IntegrableOn integrand (Icc 0 T) := integrableOn_generator_mulVec P hu hz
  let A := generator P v
  let g (s : ℝ) := A.mulVec (z (projIcc a b hab s))
  have he : EqOn g (fun s => A.mulVec (z s)) (Icc a b) := by
    intro s hs
    simp only [g, projIcc_of_mem hab hs]
  have hsub : Icc a b ⊆ Icc 0 T := Icc_subset_Icc ha hb
  have hcont : Continuous g := by
    have hZ := (continuousOn_iff_continuous_domRestrict.mp (hz.mono hsub)).comp
      (continuous_projIcc (h := hab) (a := a) (b := b))
    let L := LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)
    exact L.continuous.comp hZ
  have hLocal (t : ℝ) (ht : t ∈ Icc a b) :
      z t = z a + ∫ s in a..t, g s := by
    have hIt : IntervalIntegrable integrand volume a t :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1 (by finiteness)).mpr
        (hi.mono_set (Icc_subset_Icc ha (ht.2.trans hb)))
    have hIa : IntervalIntegrable integrand volume 0 a :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le ha (by finiteness)).mpr
        (hi.mono_set (Icc_subset_Icc_right (hab.trans hb)))
    have hs : (∫ s in a..t, integrand s) = ∫ s in a..t, g s := by
      rw [intervalIntegral.integral_of_le ht.1, intervalIntegral.integral_of_le ht.1,
        integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro s hs
      have hsab : a ≤ s ∧ s < b := ⟨hs.1.le, hs.2.trans_le ht.2⟩
      have h' := hstep hsab
      change u s = v at h'
      exact (congrArg (fun q => (generator P q).mulVec (z s)) h').trans
        (he ⟨hsab.1, hsab.2.le⟩).symm
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hIa hIt
    rw [hInt t (hsub ht), hInt a (hsub ⟨le_rfl, hab⟩), ← hsplit, hs]
    abel
  let y (t : ℝ) := z (a + t)
  have hy₀ : y 0 = z a := by simp [y]
  have hderiv (t : ℝ) (ht : t ∈ Icc 0 (b - a)) :
      HasDerivWithinAt y (A.mulVec (y t)) (Icc 0 (b - a)) t := by
    have hst (r : ℝ) (hr : r ∈ Icc 0 (b - a)) : a + r ∈ Icc a b :=
      ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have hg := intervalIntegral.integral_hasDerivAt_right
      (hcont.intervalIntegrable a (a + t)) hcont.stronglyMeasurable.stronglyMeasurableAtFilter
      (hcont.continuousAt (x := a + t))
    have hlin : HasDerivAt (fun r : ℝ => a + r) 1 t := (hasDerivAt_id t).const_add a
    have hd := (hg.scomp t hlin).const_add (z a)
    rw [one_smul, he (hst t ht)] at hd
    exact hd.hasDerivWithinAt.congr_of_mem (fun r hr => hLocal (a + r) (hst r hr)) ht
  have hs := eqOn_exp_mulVec_of_hasDerivWithinAt A (z a) y (b-a) hy₀ hderiv
    (show b-a ∈ Icc 0 (b-a) from ⟨sub_nonneg.mpr hab, le_rfl⟩)
  have hEndpoint : y (b-a) = z b := by
    unfold y
    congr 1
    ring
  exact hs.symm.trans hEndpoint

/-- A uniform step control realizes a finite product of constant-control
transitions, including the empty product when the horizon is zero. -/
theorem exists_transition_of_uniform_step (P : Plant ℝ) {n : ℕ} {h : ℝ} (hh : 0 < h)
    (values : Fin n → Fin P.controls → ℝ) {u : ℝ → Fin P.controls → ℝ}
    {z : ℝ → State P.dimension}
    (hstep : ∀ i : Fin n, EqOn u (fun _ => values i)
      (Ico ((i.val : ℝ) * h) (((i.val : ℝ) + 1) * h)))
    (hu : IntegrableOn u (Icc 0 ((n : ℝ) * h)))
    (hz : ContinuousOn z (Icc 0 ((n : ℝ) * h)))
    (hInt : ∀ t ∈ Icc 0 ((n : ℝ) * h), z t = z 0 + ∫ s in 0..t,
      (generator P (u s)).mulVec (z s)) :
    ∃ M ∈ transitionMonoid P, M.mulVec (z 0) = z ((n : ℝ) * h) := by
  have hpref (k : ℕ) (hk : k ≤ n) :
      ∃ M ∈ transitionMonoid P, M.mulVec (z 0) = z ((k : ℝ) * h) := by
    induction k with
    | zero =>
      exact ⟨1, Submonoid.one_mem _, by simp⟩
    | succ k ih =>
      let i : Fin n := ⟨k, by omega⟩
      have hab : (k : ℝ) * h ≤ ((k : ℝ) + 1) * h := by
        gcongr
        linarith
      have hb : ((k : ℝ) + 1) * h ≤ (n : ℝ) * h := by
        apply mul_le_mul_of_nonneg_right _ hh.le
        exact_mod_cast hk
      have he := segmentTransition_eq_of_integral_of_eqOn P (by positivity) hab hb
        (values i) (hstep i) hu hz hInt
      have hd : ((k : ℝ) + 1) * h - (k : ℝ) * h = h := by ring
      rw [hd] at he
      obtain ⟨M, hM, hMx⟩ := ih (by omega)
      refine ⟨segmentTransition P h (values i) * M,
        Submonoid.mul_mem _ (segmentTransition_mem P h (values i) hh.le) hM, ?_⟩
      rw [← Matrix.mulVec_mulVec, hMx, he, Nat.cast_succ]
  exact hpref n le_rfl

end ContinuousBilinear
