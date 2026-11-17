import ContinuousBilinear.CompilerGaussianEliminationProof
import ContinuousBilinear.CompilerListFoldProof

namespace ContinuousBilinear.GaussianElimination

open GaussianPivot

theorem computable_tableEntry {α : Type*} [Primcodable α]
    {t : α → Table} {i j : α → ℕ} (ht : Computable t) (hi : Computable i) (hj : Computable j) :
    Computable fun a => tableEntry (t a) (i a) (j a) :=
  computable_entry (Computable.fst.comp (Computable.snd.comp ht))
    (Computable.snd.comp (Computable.snd.comp ht)) hi hj

private theorem computable_pivotData :
    Computable fun p : (Table × Selection) × ℕ × ℕ => pivotData p.1.1 p.1.2 p.2.1 p.2.2 := by
  let P := (Table × Selection) × ℕ × ℕ
  have ht : Computable (fun p : P => p.1.1) := Computable.fst.comp Computable.fst
  have hs : Computable (fun p : P => p.1.2) := Computable.snd.comp Computable.fst
  have hi : Computable (fun p : P => p.2.1) := Computable.fst.comp Computable.snd
  have hj : Computable (fun p : P => p.2.2) := Computable.snd.comp Computable.snd
  have hrows := Computable.fst.comp hs
  have hcols := Computable.fst.comp (Computable.snd.comp hs)
  have hInv := Computable.snd.comp (Computable.snd.comp hs)
  have hB := computable_list_map hrows
    (computable_tableEntry (ht.comp Computable.fst) Computable.snd (hj.comp Computable.fst)).to₂
  have hC := computable_list_map hcols
    (computable_tableEntry (ht.comp Computable.fst) (hi.comp Computable.fst) Computable.snd).to₂
  exact (Computable.list_length.comp hrows).pair (hInv.pair (hB.pair (hC.pair
    (computable_tableEntry ht hi hj))))

private theorem primrec_notMem : PrimrecRel (fun (xs : List ℕ) (i : ℕ) => i ∉ xs) := by
  have h : PrimrecRel (fun a b : ℕ => a ≠ b) := Primrec.eq.not
  exact (PrimrecRel.forall_mem_list h).of_eq fun xs i =>
    ⟨fun h hi => h i hi rfl, fun h _ ha he => h (he ▸ ha)⟩

private theorem computable_eligible :
    Computable fun p : (Table × Selection) × ℕ × ℕ => eligible p.1.1 p.1.2 p.2.1 p.2.2 := by
  let P := (Table × Selection) × ℕ × ℕ
  have hs : Computable (fun p : P => p.1.2) := Computable.snd.comp Computable.fst
  have hrows : Computable (fun p : P => p.1.2.1) := Computable.fst.comp hs
  have hcols : Computable (fun p : P => p.1.2.2.1) := Computable.fst.comp (Computable.snd.comp hs)
  have hi : Computable (fun p : P => p.2.1) := Computable.fst.comp Computable.snd
  have hj : Computable (fun p : P => p.2.2) := Computable.snd.comp Computable.snd
  have hR := primrec_notMem.decide.to_comp.comp hrows hi
  have hC := primrec_notMem.decide.to_comp.comp hcols hj
  have hp := computablePred_eq (computable_schurComplement.comp computable_pivotData)
    (Computable.const 0)
  have h := Primrec.and.to_comp.comp hR (Primrec.and.to_comp.comp hC hp.not.decide)
  exact h.of_eq (g := fun p : P => eligible p.1.1 p.1.2 p.2.1 p.2.2)
    (fun p => by simp [eligible])

private theorem primrec_candidates : Primrec candidates := by
  unfold candidates
  apply Primrec.list_flatMap (Primrec.list_range.comp Primrec.fst)
  apply Primrec₂.curry.mp
  apply Primrec.list_map (Primrec.list_range.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
  exact ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂

private theorem computable_find {α β : Type*} [Primcodable α] [Primcodable β]
    {xs : α → List β} {test : α → β → Bool} (fallback : β)
    (hxs : Computable xs) (ht : Computable₂ test) :
    Computable fun a => (xs a).find? (test a) := by
  have htest : Computable fun p : α × β × Option β => test p.1 p.2.1 :=
    ht.comp Computable.fst (Computable.fst.comp Computable.snd)
  have hsome : Computable fun p : α × β × Option β => some p.2.1 :=
    Computable.option_some.comp (Computable.fst.comp Computable.snd)
  have hcond := Computable.cond htest hsome (Computable.snd.comp Computable.snd)
  have hstep : Computable₂ (fun a (p : β × Option β) =>
      if test a p.1 then some p.1 else p.2) :=
    (hcond.of_eq (g := fun p : α × β × Option β =>
      if test p.1 p.2.1 then some p.2.1 else p.2.2)
      (fun p => by cases test p.1 p.2.1 <;> rfl)).to₂
  have hfold := computable_list_foldr fallback hxs (Computable.const none) hstep
  exact hfold.of_eq (fun a => by
    induction xs a with
    | nil => rfl
    | cons b bs ih =>
      simp only [List.foldr_cons, List.find?_cons]
      rw [ih]
      cases test a b <;> rfl)

theorem computable_nextPivot : Computable₂ nextPivot :=
  computable_find (0, 0) (primrec_candidates.to_comp.comp Computable.fst)
    computable_eligible.to₂

private theorem computable_extend :
    Computable fun p : (Table × Selection) × ℕ × ℕ => extend p.1.1 p.1.2 p.2.1 p.2.2 := by
  let P := (Table × Selection) × ℕ × ℕ
  have hs : Computable (fun p : P => p.1.2) := Computable.snd.comp Computable.fst
  have hi : Computable (fun p : P => p.2.1) := Computable.fst.comp Computable.snd
  have hj : Computable (fun p : P => p.2.2) := Computable.snd.comp Computable.snd
  have hR := Computable.list_concat.comp (Computable.fst.comp hs) hi
  have hC := Computable.list_concat.comp (Computable.fst.comp (Computable.snd.comp hs)) hj
  have hI := computable_borderedInverse.comp computable_pivotData
  exact (hR.pair (hC.pair hI)).of_eq (g := fun p : P => extend p.1.1 p.1.2 p.2.1 p.2.2)
    (fun _ => rfl)

private theorem computable_advance : Computable₂ advance := by
  let P := Table × Selection
  have hp : Computable (fun p : P => nextPivot p.1 p.2) := computable_nextPivot
  have hstep : Computable₂ (fun (p : P) (ij : ℕ × ℕ) => extend p.1 p.2 ij.1 ij.2) :=
    computable_extend.to₂
  have h := Computable.option_casesOn hp Computable.snd hstep
  exact h.of_eq (g := fun p : P => advance p.1 p.2) (fun p => by
    unfold advance
    cases nextPivot p.1 p.2 <;> rfl)

theorem computable_stages : Computable₂ stages := by
  have hstep : Computable₂ (fun (p : Table × ℕ) (s : ℕ × Selection) => advance p.1 s.2) :=
    (computable_advance.comp (Computable.fst.comp Computable.fst)
      (Computable.snd.comp Computable.snd)).to₂
  refine (Computable.nat_rec Computable.snd
    (Computable.const (([], [], []) : Selection)) hstep).of_eq ?_
  rintro ⟨t, k⟩
  induction k with
  | zero => rfl
  | succ k ih =>
    change advance t (Nat.rec ([], [], []) (fun _ s => advance t s) k) =
      advance t (stages t k)
    rw [ih]

theorem computable_eliminate : Computable eliminate := by
  have h := computable_stages.comp Computable.id (Computable.fst : Computable (fun t : Table => t.1))
  exact h.of_eq (g := eliminate) fun _ => rfl

end ContinuousBilinear.GaussianElimination
