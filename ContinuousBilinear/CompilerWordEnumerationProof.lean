import Mathlib.Computability.Partrec

namespace ContinuousBilinear

/-- All words over the given finite alphabet up to the specified length. -/
def wordsUpTo (alphabet : List ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | k + 1 => [] :: (alphabet.flatMap fun a => (wordsUpTo alphabet k).map (a :: ·))

theorem mem_wordsUpTo (alphabet : List ℕ) (k : ℕ) (w : List ℕ) :
    w ∈ wordsUpTo alphabet k ↔ w.length ≤ k ∧ ∀ a ∈ w, a ∈ alphabet := by
  induction k generalizing w with
  | zero =>
    cases w <;> simp [wordsUpTo]
  | succ k ih =>
    cases w with
    | nil => simp [wordsUpTo]
    | cons a w =>
      simp only [wordsUpTo, List.mem_cons, List.cons_ne_nil, false_or, List.mem_flatMap,
        List.mem_map, List.cons.injEq, List.length_cons, Nat.succ_le_succ_iff]
      constructor
      · rintro ⟨b, hb, v, hv, rfl, rfl⟩
        obtain ⟨hk, hletters⟩ := (ih _).mp hv
        refine ⟨hk, ?_⟩
        intro c hc
        rcases hc with rfl | hc
        · exact hb
        · exact hletters c hc
      · rintro ⟨hk, hletters⟩
        exact ⟨a, hletters _ (Or.inl rfl), w,
          (ih _).mpr ⟨hk, fun c hc => hletters _ (Or.inr hc)⟩, rfl, rfl⟩

private def prependEach (p : ℕ × List (List ℕ)) : List (List ℕ) :=
  p.2.map (p.1 :: ·)

private theorem primrec_prependEach : Primrec prependEach :=
  Primrec.list_map Primrec.snd
    (Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂

private def extendWords (p : List ℕ × List (List ℕ)) : List (List ℕ) :=
  [] :: p.1.flatMap (fun a => prependEach (a, p.2))

private theorem primrec_extendWords : Primrec extendWords := by
  have hfold : Primrec (fun p : List ℕ × List (List ℕ) =>
      p.1.foldr (fun a ws => prependEach (a, p.2) ++ ws) []) :=
    Primrec.list_foldr Primrec.fst (Primrec.const [])
      (Primrec.list_append.comp
        (primrec_prependEach.comp ((Primrec.fst.comp Primrec.snd).pair
          (Primrec.snd.comp Primrec.fst)))
        (Primrec.snd.comp Primrec.snd)).to₂
  refine (Primrec.list_cons.comp (Primrec.const []) hfold).of_eq fun p => ?_
  unfold extendWords
  congr 1
  induction p.1 with
  | nil => rfl
  | cons a as ih => simp [ih]

theorem computable_wordsUpTo : Computable₂ wordsUpTo := by
  have hstep : Computable₂ (fun (p : List ℕ × ℕ) (state : ℕ × List (List ℕ)) =>
      extendWords (p.1, state.2)) :=
    (primrec_extendWords.to_comp.comp ((Computable.fst.comp Computable.fst).pair
      (Computable.snd.comp Computable.snd))).to₂
  change Computable (fun p : List ℕ × ℕ => wordsUpTo p.1 p.2)
  refine (Computable.nat_rec Computable.snd (Computable.const [[]]) hstep).of_eq fun p => ?_
  rcases p with ⟨a, k⟩
  induction k with
  | zero => rfl
  | succ k ih =>
    change Nat.rec [[]] (fun _ ws => extendWords (a, ws)) k = wordsUpTo a k at ih
    change extendWords (a, Nat.rec [[]] (fun _ ws => extendWords (a, ws)) k) = _
    rw [ih]
    rfl

end ContinuousBilinear
