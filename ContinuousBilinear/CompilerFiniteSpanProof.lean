import ContinuousBilinear.CompilerWordBoundProof

namespace ContinuousBilinear.PolynomialLift.LinearRepresentation

open Module Set

variable {𝕜 V ι : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

private theorem exists_bounded_independent_family {I : Type*} [FiniteDimensional 𝕜 V]
    (v : I → V) (h : Submodule.span 𝕜 (range v) = ⊤) :
    ∃ s : Fin (finrank 𝕜 V) → I, LinearIndependent 𝕜 (v ∘ s) := by
  classical
  let b := Basis.ofSpan h.ge
  let _ := FiniteDimensional.fintypeBasisIndex b
  let e := Fintype.equivFinOfCardEq (finrank_eq_card_basis b).symm
  let c := b.reindex e
  have hd : range b ⊆ range v := Basis.ofSpan_subset h.ge
  have hc (i : Fin (finrank 𝕜 V)) : c i ∈ range v :=
    hd ⟨e.symm i, by simp only [c, Basis.reindex_apply]⟩
  choose s hs using hc
  refine ⟨s, ?_⟩
  have he : v ∘ s = c := funext hs
  rw [he]
  exact c.linearIndependent

private theorem span_columns_bounded (F : LinearRepresentation 𝕜 V ι) (n : ℕ) :
    Submodule.span 𝕜 (range fun w : {w : List ι // w.length ≤ n} =>
      F.wordAction w.val F.initial) = F.wordSpan n := by
  congr 1
  ext x
  simp only [mem_range, Set.mem_ofPred_eq]
  exact ⟨fun ⟨w, h⟩ => ⟨w.val, w.property, h.symm⟩,
    fun ⟨w, hw, h⟩ => ⟨⟨w, hw⟩, h.symm⟩⟩

private theorem span_rows_bounded [FiniteDimensional 𝕜 V]
    (F : LinearRepresentation 𝕜 V ι) :
    Submodule.span 𝕜 (range fun w : {w : List ι // w.length ≤ finrank 𝕜 V} =>
      F.output.comp (F.wordAction w.val)) =
      Submodule.span 𝕜 (range fun w : List ι => F.output.comp (F.wordAction w)) := by
  have heq (w : List ι) :
      (F.dualRepresentation.wordAction w F.dualRepresentation.initial) =
        F.output.comp (F.wordAction w.reverse) := by
    ext x
    exact F.dual_wordAction w x
  have hall : (range fun w : List ι =>
      F.dualRepresentation.wordAction w F.dualRepresentation.initial) =
        range fun w : List ι => F.output.comp (F.wordAction w) := by
    ext x
    simp only [mem_range]
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨w.reverse, (heq w).symm.trans hw⟩
    · rintro ⟨w, rfl⟩
      exact ⟨w.reverse, by rw [heq, List.reverse_reverse]⟩
  have hb : (range fun w : {w : List ι // w.length ≤ finrank 𝕜 V} =>
      F.dualRepresentation.wordAction w.val F.dualRepresentation.initial) =
        range fun w : {w : List ι // w.length ≤ finrank 𝕜 V} =>
          F.output.comp (F.wordAction w.val) := by
    ext x
    simp only [mem_range]
    constructor
    · rintro ⟨w, hw⟩
      exact ⟨⟨w.val.reverse, by simpa only [List.length_reverse] using w.property⟩,
        (heq w.val).symm.trans hw⟩
    · rintro ⟨w, rfl⟩
      refine ⟨⟨w.val.reverse, by simpa only [List.length_reverse] using w.property⟩, ?_⟩
      dsimp only
      rw [heq, List.reverse_reverse]
  rw [← hall, ← hb, span_columns_bounded]
  change F.dualRepresentation.wordSpan (finrank 𝕜 V) = F.dualRepresentation.reachable
  simpa only [Subspace.dual_finrank_eq] using F.dualRepresentation.reachable_eq_wordSpan_finrank.symm

/-- The reachable span is full exactly when a dimension-sized collection of bounded
words gives linearly independent columns. -/
theorem reachable_eq_top_iff_bounded_word_basis [FiniteDimensional 𝕜 V]
    (F : LinearRepresentation 𝕜 V ι) :
    F.reachable = ⊤ ↔
      ∃ w : Fin (finrank 𝕜 V) → List ι,
        (∀ i, (w i).length ≤ finrank 𝕜 V) ∧
          LinearIndependent 𝕜 (fun i => F.wordAction (w i) F.initial) := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := exists_bounded_independent_family
      (fun w : {w : List ι // w.length ≤ finrank 𝕜 V} => F.wordAction w.val F.initial)
      (by rw [span_columns_bounded, ← F.reachable_eq_wordSpan_finrank, h])
    exact ⟨fun i => (s i).val, fun i => (s i).property, hs⟩
  · rintro ⟨w, _, hi⟩
    have hp : Submodule.span 𝕜 (range fun i => F.wordAction (w i) F.initial) ≤ F.reachable :=
      Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact F.word_mem_reachable (w i))
    rw [hi.span_eq_top_of_card_eq_finrank' (Fintype.card_fin _)] at hp
    exact top_le_iff.mp hp

/-- The observable row span is full exactly when a dimension-sized collection of
bounded words gives linearly independent rows. -/
theorem rows_span_eq_top_iff_bounded_word_basis [FiniteDimensional 𝕜 V]
    (F : LinearRepresentation 𝕜 V ι) :
    Submodule.span 𝕜 (range fun w : List ι => F.output.comp (F.wordAction w)) = ⊤ ↔
      ∃ w : Fin (finrank 𝕜 V) → List ι,
        (∀ i, (w i).length ≤ finrank 𝕜 V) ∧
          LinearIndependent 𝕜 (fun i => F.output.comp (F.wordAction (w i))) := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := exists_bounded_independent_family
      (fun w : {w : List ι // w.length ≤ finrank 𝕜 V} => F.output.comp (F.wordAction w.val))
      ((span_rows_bounded F).trans h)
    have eq : finrank 𝕜 V = finrank 𝕜 (Module.Dual 𝕜 V) := Subspace.dual_finrank_eq.symm
    let e := finCongr eq
    exact ⟨fun i => (s (e i)).val, fun i => (s (e i)).property,
      hs.comp e e.injective⟩
  · rintro ⟨w, _, hi⟩
    have hp : Submodule.span 𝕜 (range fun i => F.output.comp (F.wordAction (w i))) ≤
        Submodule.span 𝕜 (range fun w : List ι => F.output.comp (F.wordAction w)) :=
      Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨w i, rfl⟩)
    have hcard : Fintype.card (Fin (finrank 𝕜 V)) = finrank 𝕜 (Module.Dual 𝕜 V) := by
      simp only [Fintype.card_fin, Subspace.dual_finrank_eq]
    rw [hi.span_eq_top_of_card_eq_finrank' hcard] at hp
    exact top_le_iff.mp hp

end ContinuousBilinear.PolynomialLift.LinearRepresentation
