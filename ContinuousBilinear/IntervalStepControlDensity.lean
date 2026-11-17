import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Set MeasureTheory
open scoped Interval

namespace ContinuousBilinear

variable {E : Type*} [NormedAddCommGroup E]

/-- The control associated with a uniform interval partition and one value per
cell. The terminal endpoint and all points outside the cells have value zero. -/
noncomputable def intervalStepControl {n : ℕ} (h : ℝ) (values : Fin n → E) (t : ℝ) : E :=
  ∑ i : Fin n, (Ico ((i : ℕ) * h) (((i : ℕ) + 1 : ℝ) * h)).indicator
    (fun _ => values i) t

theorem intervalStepControl_eq_on_Ico {n : ℕ} {h t : ℝ} (hh : 0 < h)
    (values : Fin n → E) (i : Fin n)
    (ht : t ∈ Ico ((i : ℕ) * h) (((i : ℕ) + 1 : ℝ) * h)) :
    intervalStepControl h values t = values i := by
  classical
  unfold intervalStepControl
  rw [Finset.sum_eq_single i]
  · exact Set.indicator_of_mem ht _
  · intro j _ hji
    apply Set.indicator_of_notMem
    intro hj
    rcases lt_or_gt_of_ne hji with hlt | hgt
    · have hle : ((j : ℕ) + 1 : ℝ) ≤ (i : ℕ) := by
        exact_mod_cast (Nat.succ_le_of_lt (show j.val < i.val from hlt))
      exact ((hj.2.trans_le (mul_le_mul_of_nonneg_right hle hh.le)).not_ge) ht.1
    · have hle : ((i : ℕ) + 1 : ℝ) ≤ (j : ℕ) := by
        exact_mod_cast (Nat.succ_le_of_lt (show i.val < j.val from hgt))
      exact ((ht.2.trans_le (mul_le_mul_of_nonneg_right hle hh.le)).not_ge) hj.1
  · simp

theorem integrable_intervalStepControl {n : ℕ} (h : ℝ) (values : Fin n → E) :
    Integrable (intervalStepControl h values) volume := by
  apply integrable_finsetSum
  intro i _
  apply IntegrableOn.integrable_indicator _ measurableSet_Ico
  exact integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)

private theorem exists_cell_of_mem_Ico {n : ℕ} {h t : ℝ} (hh : 0 < h)
    (ht : t ∈ Ico (0 : ℝ) ((n : ℝ) * h)) :
    ∃ i : Fin n, t ∈ Ico ((i : ℕ) * h) (((i : ℕ) + 1 : ℝ) * h) := by
  have hdiv : 0 ≤ t / h := div_nonneg ht.1 hh.le
  let j := ⌊t / h⌋₊
  have hj : j < n := (Nat.floor_lt hdiv).mpr ((div_lt_iff₀ hh).mpr ht.2)
  refine ⟨⟨j, hj⟩, ?_, ?_⟩
  · exact (le_div_iff₀ hh).mp (Nat.floor_le hdiv)
  · exact (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one _)

variable [NormedSpace ℝ E]

/-- Finite uniform interval step controls are dense in the finite-horizon
integrable controls. Values at the right endpoint do not affect the integral. -/
theorem exists_intervalStepControl_integral_norm_sub_lt {T ε : ℝ} (hT : 0 < T)
    (hε : 0 < ε) {u : ℝ → E} (hu : IntegrableOn u (Icc 0 T)) :
    ∃ n : ℕ, 0 < n ∧ ∃ values : Fin n → E,
      IntegrableOn (intervalStepControl (T / n) values) (Icc 0 T) ∧
      (∫ t in (0 : ℝ)..T, ‖u t - intervalStepControl (T / n) values t‖) < ε := by
  obtain ⟨g, hclose, hg⟩ := hu.exists_boundedContinuous_integral_sub_le
    (show 0 < ε / 4 by positivity)
  have hclose' : (∫ t in (0 : ℝ)..T, ‖u t - g t‖) ≤ ε / 4 := by
    rw [intervalIntegral.integral_of_le hT.le, ← integral_Icc_eq_integral_Ioc]
    exact hclose
  let η := ε / (4 * T)
  have hη : 0 < η := by unfold η; positivity
  have hgc : Continuous (g : ℝ → E) := g.continuous
  obtain ⟨δ, hδ, hgcδ⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous
      (hgc.continuousOn : ContinuousOn (g : ℝ → E) (Icc 0 T))) η hη
  obtain ⟨n, hn⟩ := exists_nat_gt (T / δ)
  have hnR : 0 < (n : ℝ) := (div_pos hT hδ).trans hn
  have hnN : 0 < n := by exact_mod_cast hnR
  let h := T / (n : ℝ)
  have hh : 0 < h := div_pos hT hnR
  have hsmall : h < δ := (div_lt_iff₀ hnR).mpr
    (by simpa only [mul_comm] using (div_lt_iff₀ hδ).mp hn)
  have htotal : (n : ℝ) * h = T := by
    dsimp [h]
    field_simp
  let values (i : Fin n) := g ((i : ℕ) * h)
  let v := intervalStepControl h values
  have hv : IntegrableOn v (Icc 0 T) := (integrable_intervalStepControl h values).integrableOn
  have hsample (t : ℝ) (ht : t ∈ Ioo 0 T) : ‖g t - v t‖ ≤ η := by
    have hcell : t ∈ Ico (0 : ℝ) ((n : ℝ) * h) := by
      rw [htotal]
      exact ⟨ht.1.le, ht.2⟩
    obtain ⟨i, hi⟩ := exists_cell_of_mem_Ico hh hcell
    change ‖g t - intervalStepControl h values t‖ ≤ η
    rw [intervalStepControl_eq_on_Ico hh values i hi]
    have hs : ((i : ℕ) * h : ℝ) ∈ Icc 0 T := by
      refine ⟨mul_nonneg (Nat.cast_nonneg _) hh.le, ?_⟩
      exact hi.1.trans ht.2.le
    have hdist : dist t ((i : ℕ) * h) < δ := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hi.1)]
      apply lt_trans _ hsmall
      linarith [hi.2]
    rw [show values i = g ((i : ℕ) * h) from rfl, ← dist_eq_norm]
    exact (hgcδ t ⟨ht.1.le, ht.2.le⟩ _ hs hdist).le
  let toInterval {f : ℝ → ℝ} (hf : IntegrableOn f (Icc 0 T)) :
      IntervalIntegrable f volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le (by finiteness)).mpr hf
  have huv : IntervalIntegrable (fun t => ‖u t - v t‖) volume 0 T :=
    toInterval (hu.sub hv).norm
  have hug : IntervalIntegrable (fun t => ‖u t - g t‖) volume 0 T :=
    toInterval (hu.sub hg).norm
  have hgv : IntervalIntegrable (fun t => ‖g t - v t‖) volume 0 T :=
    toInterval (hg.sub hv).norm
  have hsampleInt : (∫ t in (0 : ℝ)..T, ‖g t - v t‖) ≤ η * T := by
    have hle := intervalIntegral.integral_mono_on_of_le_Ioo hT.le hgv
      (intervalIntegrable_const (c := η)) hsample
    simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] using hle
  have hbound : (∫ t in (0 : ℝ)..T, ‖u t - v t‖) ≤ ε / 4 + η * T := by
    calc
      _ ≤ ∫ t in (0 : ℝ)..T, (‖u t - g t‖ + ‖g t - v t‖) :=
        intervalIntegral.integral_mono_on hT.le huv (hug.add hgv)
          (fun t _ => by
            rw [show u t - v t = (u t - g t) + (g t - v t) by abel]
            exact norm_add_le _ _)
      _ ≤ _ := by
        rw [intervalIntegral.integral_add hug hgv]
        exact add_le_add hclose' hsampleInt
  have hprod : η * T = ε / 4 := by
    dsimp [η]
    field_simp
  exact ⟨n, hnN, values, hv, hbound.trans_lt (by rw [hprod]; linarith)⟩

end ContinuousBilinear

