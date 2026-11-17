import ContinuousBilinear.CompilerWordAgreementProof

namespace ContinuousBilinear.RationalFeedbackCode

open PolynomialLift Module

noncomputable section

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {n m : ℕ}

/-- Encode a rational representation in a chosen basis and preserve the channel order. -/
@[reducible] def encodeRepresentation (F : LinearRepresentation ℚ V (Fin m)) (b : Basis (Fin n) ℚ V) :
    RationalFeedbackCode :=
  (n, List.ofFn (b.equivFun F.initial), List.ofFn (fun j => F.output (b j)),
    List.ofFn fun k => PlantCode.matrixEntries (F.coordinateOperators b k))

private theorem encodeRepresentation_channels (F : LinearRepresentation ℚ V (Fin m))
    (b : Basis (Fin n) ℚ V) : (encodeRepresentation F b).2.2.2.length = m :=
  List.length_ofFn

private theorem encodeRepresentation_initial (F : LinearRepresentation ℚ V (Fin m))
    (b : Basis (Fin n) ℚ V) : (encodeRepresentation F b).initial = b.equivFun F.initial := by
  funext i
  have hi : i.val < n := i.isLt
  simp [initial, encodeRepresentation, hi]

private theorem encodeRepresentation_output_row (F : LinearRepresentation ℚ V (Fin m))
    (b : Basis (Fin n) ℚ V) (i : Fin n) :
    (encodeRepresentation F b).output i = F.output (b i) := by
  simp [output, encodeRepresentation, i.isLt]

private theorem encodeRepresentation_operator (F : LinearRepresentation ℚ V (Fin m))
    (b : Basis (Fin n) ℚ V) (i : Fin (encodeRepresentation F b).2.2.2.length) :
    (encodeRepresentation F b).operator i =
      F.coordinateOperators b (Fin.cast (encodeRepresentation_channels F b) i) := by
  apply Matrix.ext
  intro j k
  let entries := List.ofFn fun l => PlantCode.matrixEntries (F.coordinateOperators b l)
  have hk : entries[i.val] = PlantCode.matrixEntries
      (F.coordinateOperators b (Fin.cast (encodeRepresentation_channels F b) i)) := by
    simp only [entries, List.getElem_ofFn]
    rfl
  change (entries[i.val]).getD (j.val * n + k.val) 0 = _
  rw [hk]
  exact PlantCode.matrixEntries_getD _ _ _ _

private theorem encodeRepresentation_operator_apply (F : LinearRepresentation ℚ V (Fin m))
    (b : Basis (Fin n) ℚ V) (i : Fin (encodeRepresentation F b).2.2.2.length) (x : V) :
    (encodeRepresentation F b).representation.operator i (b.equivFun x) =
      b.equivFun (F.operator (Fin.cast (encodeRepresentation_channels F b) i) x) := by
  change ((encodeRepresentation F b).operator i).mulVec (b.equivFun x) = _
  rw [encodeRepresentation_operator]
  exact LinearMap.toMatrix_mulVec_repr b b _ x

private theorem encodeRepresentation_coordinates_word (F : LinearRepresentation ℚ V (Fin m))
    (b : Basis (Fin n) ℚ V) (w : List (Fin (encodeRepresentation F b).2.2.2.length)) (x : V) :
    (encodeRepresentation F b).representation.wordAction w (b.equivFun x) =
      b.equivFun (F.wordAction (w.map (Fin.cast (encodeRepresentation_channels F b))) x) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    let E := (encodeRepresentation F b).representation
    let j := Fin.cast (encodeRepresentation_channels F b) a
    change E.operator a (E.wordAction w (b.equivFun x)) =
      b.equivFun (F.operator j (F.wordAction (w.map (Fin.cast (encodeRepresentation_channels F b))) x))
    exact (congrArg (E.operator a) ih).trans (encodeRepresentation_operator_apply F b a _)

private theorem encodeRepresentation_output (F : LinearRepresentation ℚ V (Fin m))
    (b : Basis (Fin n) ℚ V) (x : V) :
    (encodeRepresentation F b).representation.output (b.equivFun x) = F.output x := by
  change (∑ i, (encodeRepresentation F b).output i * b.equivFun x i) = _
  have he (i : Fin n) := encodeRepresentation_output_row F b i
  simp_rw [he]
  have h := congrArg F.output (b.sum_repr x)
  simp only [map_sum, map_smul, smul_eq_mul] at h
  exact (Finset.sum_congr rfl (fun i _ => mul_comm _ _)).trans h

private theorem encodeRepresentation_wordOutput (F : LinearRepresentation ℚ V (Fin m))
    (b : Basis (Fin n) ℚ V) (w : List (Fin (encodeRepresentation F b).2.2.2.length)) :
    (encodeRepresentation F b).wordOutput (w.map Fin.val) =
      F.output (F.wordAction (w.map (Fin.cast (encodeRepresentation_channels F b))) F.initial) := by
  rw [wordOutput_eq]
  change (encodeRepresentation F b).representation.output
    ((encodeRepresentation F b).representation.wordAction w (encodeRepresentation F b).initial) = _
  rw [encodeRepresentation_initial, encodeRepresentation_coordinates_word, encodeRepresentation_output]

private theorem exists_word_of_map_val {m : ℕ} (w : List ℕ) (h : ∀ i ∈ w, i < m) :
    ∃ v : List (Fin m), v.map Fin.val = w := by
  induction w with
  | nil => exact ⟨[], rfl⟩
  | cons i w ih =>
    rcases ih (fun j hj => h j (List.mem_cons_of_mem _ hj)) with ⟨v, hv⟩
    exact ⟨⟨i, h i List.mem_cons_self⟩ :: v, by simp [hv]⟩

private theorem encodeRepresentation_reachable (F : LinearRepresentation ℚ V (Fin m))
    (b : Basis (Fin n) ℚ V) (hc : F.reachable = ⊤) :
    (encodeRepresentation F b).representation.reachable = ⊤ := by
  let E := (encodeRepresentation F b).representation
  let e := b.equivFun
  let l := finCongr (encodeRepresentation_channels F b)
  have hl (w : List (Fin m)) :
      (w.map l.symm).map (Fin.cast (encodeRepresentation_channels F b)) = w := by
    rw [List.map_map]
    have h : Fin.cast (encodeRepresentation_channels F b) ∘ l.symm = id :=
      funext l.apply_symm_apply
    rw [h, List.map_id]
  have hg (w : List (Fin m)) :
      e (F.wordAction w F.initial) ∈ E.reachable := by
    have h := E.word_mem_reachable (w.map l.symm)
    change (encodeRepresentation F b).representation.wordAction _
      (encodeRepresentation F b).initial ∈ E.reachable at h
    rw [encodeRepresentation_initial, encodeRepresentation_coordinates_word] at h
    rw [hl] at h
    exact h
  have hs : F.reachable ≤ E.reachable.comap e.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    exact hg w
  rw [Submodule.eq_top_iff']
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  exact hs (hc ▸ Submodule.mem_top : y ∈ F.reachable)

private theorem encodeRepresentation_observable (F : LinearRepresentation ℚ V (Fin m))
    (b : Basis (Fin n) ℚ V)
    (ho : Submodule.span ℚ (Set.range fun w : List (Fin m) =>
      F.output.comp (F.wordAction w)) = ⊤) :
    Submodule.span ℚ (Set.range fun w =>
      (encodeRepresentation F b).representation.output.comp
        ((encodeRepresentation F b).representation.wordAction w)) = ⊤ := by
  let E := (encodeRepresentation F b).representation
  let e := b.equivFun
  let l := finCongr (encodeRepresentation_channels F b)
  have hl (w : List (Fin m)) :
      (w.map l.symm).map (Fin.cast (encodeRepresentation_channels F b)) = w := by
    rw [List.map_map]
    have h : Fin.cast (encodeRepresentation_channels F b) ∘ l.symm = id :=
      funext l.apply_symm_apply
    rw [h, List.map_id]
  let transfer : (V →ₗ[ℚ] ℚ) →ₗ[ℚ] ((Fin n → ℚ) →ₗ[ℚ] ℚ) :=
    (e.symm : (Fin n → ℚ) →ₗ[ℚ] V).dualMap
  let W := Submodule.span ℚ (Set.range fun w => E.output.comp (E.wordAction w))
  have hg (w : List (Fin m)) : transfer (F.output.comp (F.wordAction w)) ∈ W := by
    have he : transfer (F.output.comp (F.wordAction w)) =
        E.output.comp (E.wordAction (w.map l.symm)) := by
      apply LinearMap.ext
      intro x
      obtain ⟨y, rfl⟩ := e.surjective x
      change F.output (F.wordAction w (e.symm (e y))) =
        (encodeRepresentation F b).representation.output
          ((encodeRepresentation F b).representation.wordAction _ (b.equivFun y))
      rw [LinearEquiv.symm_apply_apply, encodeRepresentation_coordinates_word,
        encodeRepresentation_output]
      rw [hl]
    rw [he]
    exact Submodule.subset_span ⟨_, rfl⟩
  have hs : Submodule.span ℚ (Set.range fun w : List (Fin m) =>
        F.output.comp (F.wordAction w)) ≤ W.comap transfer := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    exact hg w
  change W = ⊤
  rw [Submodule.eq_top_iff']
  intro φ
  let x : V →ₗ[ℚ] ℚ := φ.comp e.toLinearMap
  have hφ : transfer x = φ := by
    apply LinearMap.ext
    intro y
    change φ (e (e.symm y)) = φ y
    rw [LinearEquiv.apply_symm_apply]
  rw [← hφ]
  exact hs (ho ▸ Submodule.mem_top : x ∈ _)

private theorem encodeRepresentation_commute (F : LinearRepresentation ℚ V (Fin m))
    (b : Basis (Fin n) ℚ V) (h : ∀ i j, Commute (F.operator i) (F.operator j)) :
    ∀ i j, Commute ((encodeRepresentation F b).operator i)
      ((encodeRepresentation F b).operator j) := by
  intro i j
  rw [encodeRepresentation_operator, encodeRepresentation_operator]
  let a := Fin.cast (encodeRepresentation_channels F b) i
  let c := Fin.cast (encodeRepresentation_channels F b) j
  change LinearMap.toMatrix b b (F.operator a) * LinearMap.toMatrix b b (F.operator c) =
    LinearMap.toMatrix b b (F.operator c) * LinearMap.toMatrix b b (F.operator a)
  rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp]
  exact congrArg (LinearMap.toMatrix b b) (h a c).eq

/-- Any rational basis of the reachable/observable quotient gives an
encoding that preserves the words and has full reachable and observable spans. -/
theorem encodeMinimalRepresentation_correct (source : RationalFeedbackCode)
    (b : Basis (Fin n) ℚ (source.representation.reachable ⧸ source.representation.unobservable))
    (hcomm : ∀ i j, Commute (source.operator i) (source.operator j)) :
    let target := encodeRepresentation source.representation.minimalRepresentation b
    wordOutputsAgree (source, target) ∧
      (∀ i j, Commute (target.operator i) (target.operator j)) ∧
      target.representation.reachable = ⊤ ∧
      Submodule.span ℚ (Set.range fun w =>
        target.representation.output.comp (target.representation.wordAction w)) = ⊤ := by
  let F := source.representation
  let G := F.minimalRepresentation
  let target := encodeRepresentation G b
  have hF (i j : Fin source.2.2.2.length) : Commute (F.operator i) (F.operator j) := by
    change F.operator i * F.operator j = F.operator j * F.operator i
    apply LinearMap.ext
    intro x
    change (source.operator i).mulVec ((source.operator j).mulVec x) =
      (source.operator j).mulVec ((source.operator i).mulVec x)
    simp only [Matrix.mulVec_mulVec, (hcomm i j).eq]
  refine ⟨?_, encodeRepresentation_commute G b (fun i j => F.minimal_commute i j (hF i j)),
    encodeRepresentation_reachable G b F.minimal_words_span,
    encodeRepresentation_observable G b F.minimal_rows_span⟩
  have hm : target.2.2.2.length = source.2.2.2.length := encodeRepresentation_channels G b
  refine ⟨hm.symm, ?_⟩
  intro w hw
  have hletters := ((mem_wordsUpTo _ _ _).mp hw).2
  obtain ⟨v, hv⟩ := exists_word_of_map_val (m := target.2.2.2.length) w
    (fun i hi => hm.symm ▸ List.mem_range.mp (hletters i hi))
  rw [← hv]
  have hg := encodeRepresentation_wordOutput G b v
  have hf := source.wordOutput_eq (v.map (Fin.cast hm))
  rw [List.map_map] at hf
  change source.wordOutput (v.map Fin.val) = _ at hf
  exact hf.trans ((F.minimal_output_word _).symm.trans hg.symm)


/-- The reachable and observable quotient admits a finite rational encoding
with identical word coefficients and commuting operators. -/
theorem exists_minimal_wordOutputsAgree (source : RationalFeedbackCode)
    (hcomm : ∀ i j, Commute (source.operator i) (source.operator j)) :
    ∃ target : RationalFeedbackCode, wordOutputsAgree (source, target) ∧
      (∀ i j, Commute (target.operator i) (target.operator j)) ∧
      target.representation.reachable = ⊤ ∧
      Submodule.span ℚ (Set.range fun w =>
        target.representation.output.comp (target.representation.wordAction w)) = ⊤ := by
  let F := source.representation
  let b := Module.finBasis ℚ (F.reachable ⧸ F.unobservable)
  exact ⟨encodeRepresentation F.minimalRepresentation b,
    encodeMinimalRepresentation_correct source b hcomm⟩

end
end ContinuousBilinear.RationalFeedbackCode
