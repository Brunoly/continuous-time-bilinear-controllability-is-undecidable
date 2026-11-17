import ContinuousBilinear.PolynomialLiftQuotient

namespace ContinuousBilinear.PolynomialLift.LinearRepresentation

variable {𝕜 V ι : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- Span of the vectors obtained from words of length at most the given bound. -/
def wordSpan (F : LinearRepresentation 𝕜 V ι) (k : ℕ) : Submodule 𝕜 V :=
  Submodule.span 𝕜 {x | ∃ w : List ι, w.length ≤ k ∧ x = F.wordAction w F.initial}

theorem wordSpan_mono (F : LinearRepresentation 𝕜 V ι) : Monotone F.wordSpan := by
  intro k l h
  apply Submodule.span_mono
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w, hw.trans h, rfl⟩

theorem wordSpan_le_reachable (F : LinearRepresentation 𝕜 V ι) (k : ℕ) :
    F.wordSpan k ≤ F.reachable := by
  apply Submodule.span_le.mpr
  rintro _ ⟨w, _, rfl⟩
  exact F.word_mem_reachable w

private theorem operator_mem_wordSpan_succ (F : LinearRepresentation 𝕜 V ι)
    (k : ℕ) (i : ι) {x : V} (hx : x ∈ F.wordSpan k) :
    F.operator i x ∈ F.wordSpan (k + 1) := by
  induction hx using Submodule.span_induction with
  | mem _ hw =>
    rcases hw with ⟨w, hw, rfl⟩
    exact Submodule.subset_span ⟨i :: w, Nat.succ_le_succ hw, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => simpa only [map_add] using (F.wordSpan (k + 1)).add_mem hx hy
  | smul a x _ hx => simpa only [map_smul] using (F.wordSpan (k + 1)).smul_mem a hx

theorem reachable_eq_wordSpan_of_stabilizes (F : LinearRepresentation 𝕜 V ι)
    (k : ℕ) (h : F.wordSpan k = F.wordSpan (k + 1)) :
    F.reachable = F.wordSpan k := by
  refine le_antisymm ?_ (F.wordSpan_le_reachable k)
  apply Submodule.span_le.mpr
  rintro _ ⟨w, rfl⟩
  induction w with
  | nil => exact Submodule.subset_span ⟨[], Nat.zero_le k, rfl⟩
  | cons i w ih => exact h.symm ▸ F.operator_mem_wordSpan_succ k i ih

/-- Ambient dimension bounds the word length needed to generate the reachable space. -/
theorem reachable_eq_wordSpan_finrank [Module.Finite 𝕜 V]
    (F : LinearRepresentation 𝕜 V ι) :
    F.reachable = F.wordSpan (Module.finrank 𝕜 V) := by
  let n := Module.finrank 𝕜 V
  have hex : ∃ k ≤ n, F.wordSpan k = F.wordSpan (k + 1) := by
    by_contra! h
    have hlower (k : ℕ) (hk : k ≤ n + 1) : k ≤ Module.finrank 𝕜 (F.wordSpan k) := by
      induction k with
      | zero => exact Nat.zero_le _
      | succ k ih =>
        have hlt : F.wordSpan k < F.wordSpan (k + 1) :=
          lt_of_le_of_ne (F.wordSpan_mono (Nat.le_succ k)) (h k (by omega))
        have hr := Submodule.finrank_lt_finrank_of_lt hlt
        exact Nat.succ_le_of_lt ((ih (by omega)).trans_lt hr)
    have hmax := Submodule.finrank_le (F.wordSpan (n + 1))
    have hmin := hlower (n + 1) le_rfl
    omega
  rcases hex with ⟨k, hk, heq⟩
  refine le_antisymm ?_ (F.wordSpan_le_reachable n)
  rw [F.reachable_eq_wordSpan_of_stabilizes k heq]
  exact F.wordSpan_mono hk

/-- The transpose action on output rows reverses the order of a word. -/
def dualRepresentation (F : LinearRepresentation 𝕜 V ι) :
    LinearRepresentation 𝕜 (Module.Dual 𝕜 V) ι where
  operator i := (F.operator i).dualMap
  initial := F.output
  output := 0

theorem dual_wordAction (F : LinearRepresentation 𝕜 V ι)
    (w : List ι) (x : V) :
    (F.dualRepresentation.wordAction w F.output) x = F.output (F.wordAction w.reverse x) := by
  induction w generalizing x with
  | nil => rfl
  | cons i w ih =>
    rw [wordAction_cons]
    change (F.dualRepresentation.wordAction w F.output) (F.operator i x) = _
    rw [ih, List.reverse_cons, wordAction_append, wordAction_cons, wordAction_nil]

/-- Testing output vanishing on words up to the ambient dimension suffices. -/
theorem all_output_word_zero_of_bounded [Module.Finite 𝕜 V]
    (F : LinearRepresentation 𝕜 V ι) (x : V)
    (h : ∀ w : List ι, w.length ≤ Module.finrank 𝕜 V → F.output (F.wordAction w x) = 0) :
    ∀ w : List ι, F.output (F.wordAction w x) = 0 := by
  let ev : Module.Dual 𝕜 V →ₗ[𝕜] 𝕜 :=
    { toFun := fun a => a x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hker : F.dualRepresentation.reachable ≤ LinearMap.ker ev := by
    rw [F.dualRepresentation.reachable_eq_wordSpan_finrank]
    apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    change (F.dualRepresentation.wordAction w F.output) x = 0
    rw [F.dual_wordAction]
    apply h
    simpa using hw
  intro w
  have hw := hker (F.dualRepresentation.word_mem_reachable w.reverse)
  change (F.dualRepresentation.wordAction w.reverse F.output) x = 0 at hw
  simpa only [F.dual_wordAction, List.reverse_reverse] using hw

end ContinuousBilinear.PolynomialLift.LinearRepresentation
