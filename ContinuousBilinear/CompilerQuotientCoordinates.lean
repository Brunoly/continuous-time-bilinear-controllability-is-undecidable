import ContinuousBilinear.CompilerHankelProof

namespace ContinuousBilinear.PolynomialLift.LinearRepresentation

open Module

variable {𝕜 V ι : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

/-- The output functionals indexed by a finite family of words. -/
def wordObservationMap (F : LinearRepresentation 𝕜 V ι) {n : ℕ}
    (u : Fin n → List ι) : V →ₗ[𝕜] (Fin n → 𝕜) :=
  LinearMap.pi fun i => F.output.comp (F.wordAction (u i))

/-- Outputs of the represented word with the selected words prepended. -/
def wordObservations (F : LinearRepresentation 𝕜 V ι) {n : ℕ}
    (u : Fin n → List ι) (w : List ι) : Fin n → 𝕜 :=
  fun i => F.output (F.wordAction (u i ++ w) F.initial)

theorem wordObservationMap_word (F : LinearRepresentation 𝕜 V ι) {n : ℕ}
    (u : Fin n → List ι) (w : List ι) :
    F.wordObservationMap u (F.wordAction w F.initial) = F.wordObservations u w := by
  funext i
  exact (congrArg F.output (F.wordAction_append (u i) w F.initial)).symm

theorem wordHankel_col_eq_wordObservations (F : LinearRepresentation 𝕜 V ι) {n : ℕ}
    (u v : Fin n → List ι) (j : Fin n) :
    (F.wordHankel u v).col j = F.wordObservations u (v j) := rfl

/-- The selected suffix states form a basis of the reachable/observable
quotient when all residual entries of the bounded Hankel table vanish. -/
theorem exists_quotientBasis_of_schurComplement_eq_zero
    [FiniteDimensional 𝕜 V] (F : LinearRepresentation 𝕜 V ι) {n k : ℕ}
    (u v : Fin n → List ι) (R : Matrix (Fin n) (Fin n) 𝕜)
    (hH : F.wordHankel u v * R = 1) (hR : R * F.wordHankel u v = 1)
    (hk : Module.finrank 𝕜 V ≤ k)
    (hResidual : ∀ a b : List ι, a.length ≤ k → b.length ≤ k →
      F.output (F.wordAction (a ++ b) F.initial) =
        ∑ j, F.output (F.wordAction (a ++ v j) F.initial) * (R.mulVec (F.wordObservations u b)) j) :
    ∃ B : Basis (Fin n) 𝕜 (F.reachable ⧸ F.unobservable),
      ∀ j, B j = F.minimalRepresentation.wordAction (v j) F.minimalRepresentation.initial := by
  let G := F.minimalRepresentation
  let z (j : Fin n) := G.wordAction (v j) G.initial
  have hwords (w : List ι) : G.output (G.wordAction w G.initial) =
      F.output (F.wordAction w F.initial) := F.minimal_output_word w
  have hobs (a b : List ι) :
      G.output (G.wordAction a (G.wordAction b G.initial)) =
        F.output (F.wordAction (a ++ b) F.initial) := by
    rw [← G.wordAction_append, hwords]
  have hHG : G.wordHankel u v = F.wordHankel u v := by
    ext i j
    exact hwords (u i ++ v j)
  have hImage : G.wordObservationMap u ∘ z = (F.wordHankel u v).col := by
    funext j
    rw [Function.comp_apply, wordObservationMap_word, ← wordHankel_col_eq_wordObservations, hHG]
  have hUnit : IsUnit (F.wordHankel u v) :=
    ⟨⟨_, R, hH, hR⟩, rfl⟩
  have hIndependent : LinearIndependent 𝕜 z := by
    apply LinearIndependent.of_comp (G.wordObservationMap u)
    rw [hImage, Matrix.linearIndependent_cols_iff_isUnit]
    exact hUnit
  have hDim : Module.finrank 𝕜 (F.reachable ⧸ F.unobservable) ≤ k :=
    F.unobservable.finrank_quotient_le.trans (F.reachable.finrank_le.trans hk)
  have hRep (w : List ι) (hw : w.length ≤ k) :
      G.wordAction w G.initial = ∑ j, (R.mulVec (F.wordObservations u w)) j • z j := by
    apply sub_eq_zero.mp
    apply F.minimal_word_separates
    apply G.all_output_word_zero_of_bounded
    intro a ha
    simp only [map_sub, map_sum, map_smul, smul_eq_mul, z]
    simp_rw [hobs]
    rw [hResidual a w (ha.trans hDim) hw]
    simp only [sub_eq_zero]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hSpan : ⊤ ≤ Submodule.span 𝕜 (Set.range z) := by
    rw [← F.minimal_words_span, G.reachable_eq_wordSpan_finrank]
    apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    rw [hRep w (hw.trans hDim)]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self j))
  exact ⟨Basis.mk hIndependent hSpan, fun j => Basis.mk_apply hIndependent hSpan j⟩

/-- In a basis of suffix states, the selected observations give the coordinate
system solved by the rational elimination. -/
theorem wordHankel_mulVec_equivFun (F : LinearRepresentation 𝕜 V ι) {n : ℕ}
    (u v : Fin n → List ι) (B : Basis (Fin n) 𝕜 V)
    (hB : ∀ j, B j = F.wordAction (v j) F.initial) (x : V) :
    (F.wordHankel u v).mulVec (B.equivFun x) = F.wordObservationMap u x := by
  funext i
  have h := congrArg (F.output.comp (F.wordAction (u i))) (B.sum_repr x)
  simp only [map_sum, map_smul, LinearMap.comp_apply, smul_eq_mul] at h
  change (∑ j, F.output (F.wordAction (u i ++ v j) F.initial) * B.equivFun x j) =
    F.output (F.wordAction (u i) x)
  rw [← h]
  apply Finset.sum_congr rfl
  intro j _
  rw [hB, ← F.wordAction_append]
  exact mul_comm _ _

theorem equivFun_eq_inverseHankel_mulVec (F : LinearRepresentation 𝕜 V ι) {n : ℕ}
    (u v : Fin n → List ι) (B : Basis (Fin n) 𝕜 V)
    (hB : ∀ j, B j = F.wordAction (v j) F.initial)
    (R : Matrix (Fin n) (Fin n) 𝕜) (hR : R * F.wordHankel u v = 1) (x : V) :
    B.equivFun x = R.mulVec (F.wordObservationMap u x) := by
  rw [← wordHankel_mulVec_equivFun F u v B hB x, Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]

end ContinuousBilinear.PolynomialLift.LinearRepresentation
