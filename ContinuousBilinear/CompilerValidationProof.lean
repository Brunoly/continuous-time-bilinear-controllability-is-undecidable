import ContinuousBilinear.EncodingProof
import ContinuousBilinear.CompilerIntegerArithmeticProof
import Mathlib.Order.Interval.Finset.Nat

namespace ContinuousBilinear

namespace PlantCode

private theorem primrec_forall_lt {α : Type*} [Primcodable α] {n : α → ℕ}
    {p : α × ℕ → Prop} (hn : Primrec n) (hp : PrimrecPred p) :
    PrimrecPred fun a => ∀ i < n a, p (a, i) := by
  have hentries : Primrec fun a => (List.range (n a)).map (fun i => (a, i)) :=
    Primrec.list_map (Primrec.list_range.comp hn) Primrec.id.to₂
  exact ((PrimrecPred.forall_mem_list hp).comp hentries).of_eq fun a => by simp

private theorem primrec_sum_range {α : Type*} [Primcodable α] {n : α → ℕ}
    {f : α × ℕ → ℤ} (hn : Primrec n) (hf : Primrec f) :
    Primrec fun a => ((List.range (n a)).map (fun i => f (a, i))).sum := by
  have hsum : Primrec (fun l : List ℤ => l.sum) := by
    have hfold : Primrec fun l : List ℤ => l.foldr (· + ·) 0 :=
      Primrec.list_foldr Primrec.id (Primrec.const 0)
        ((Primrec₂.uncurry.mpr primrec_int_add).comp Primrec.snd).to₂
    apply hfold.of_eq
    intro l
    induction l with
    | nil => rfl
    | cons x xs ih => simp [ih]
  exact hsum.comp (Primrec.list_map (Primrec.list_range.comp hn) hf.to₂)

private def entry (p : (ℕ × List ℤ) × ℕ × ℕ) : ℤ :=
  p.1.2.getD (p.2.1 * p.1.1 + p.2.2) 0

private theorem primrec_entry : Primrec entry :=
  (Primrec.option_getD.comp
    (Primrec.list_getElem?.comp (Primrec.snd.comp Primrec.fst)
      (Primrec.nat_add.comp (Primrec.nat_mul.comp
        (Primrec.fst.comp Primrec.snd) (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.snd)))
    (Primrec.const 0)).of_eq fun _ => rfl

private def productEntry (p : ((ℕ × List ℤ × List ℤ) × ℕ) × ℕ) : ℤ :=
  (((List.range p.1.1.1).map fun k =>
    entry ((p.1.1.1, p.1.1.2.1), p.1.2, k) *
    entry ((p.1.1.1, p.1.1.2.2), k, p.2))).sum

set_option maxHeartbeats 1500000 in
private theorem primrec_productEntry : Primrec productEntry := by
  let hn : Primrec (fun p : ((ℕ × List ℤ × List ℤ) × ℕ) × ℕ => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  let hAB : Primrec (fun p : (((ℕ × List ℤ × List ℤ) × ℕ) × ℕ) × ℕ => p.1.1.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
  let hn' := hn.comp (Primrec.fst :
    Primrec (Prod.fst : ((((ℕ × List ℤ × List ℤ) × ℕ) × ℕ) × ℕ) →
      ((ℕ × List ℤ × List ℤ) × ℕ) × ℕ))
  exact primrec_sum_range hn (primrec_int_mul.comp
    (primrec_entry.comp ((hn'.pair (Primrec.fst.comp hAB)).pair
      ((Primrec.snd.comp (Primrec.fst.comp Primrec.fst)).pair Primrec.snd)))
    (primrec_entry.comp ((hn'.pair (Primrec.snd.comp hAB)).pair
      (Primrec.snd.pair (Primrec.snd.comp Primrec.fst)))))

private def commuteEntries (p : ℕ × List ℤ × List ℤ) : Prop :=
  ∀ i < p.1, ∀ j < p.1, productEntry ((p, i), j) = productEntry (((p.1, p.2.2, p.2.1), i), j)

private theorem primrec_commuteEntries : PrimrecPred commuteEntries := by
  unfold commuteEntries
  refine primrec_forall_lt
    (p := fun p : (ℕ × List ℤ × List ℤ) × ℕ => ∀ j < p.1.1,
      productEntry (p, j) = productEntry (((p.1.1, p.1.2.2, p.1.2.1), p.2), j))
    Primrec.fst ?_
  refine primrec_forall_lt
    (p := fun p : ((ℕ × List ℤ × List ℤ) × ℕ) × ℕ =>
      productEntry p = productEntry (((p.1.1.1, p.1.1.2.2, p.1.1.2.1), p.1.2), p.2))
    (Primrec.fst.comp Primrec.fst) ?_
  have hp : Primrec (fun p : ((ℕ × List ℤ × List ℤ) × ℕ) × ℕ => p.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hswap : Primrec fun p : ℕ × List ℤ × List ℤ => (p.1, p.2.2, p.2.1) :=
    Primrec.fst.pair ((Primrec.snd.comp Primrec.snd).pair (Primrec.fst.comp Primrec.snd))
  exact Primrec.eq.comp primrec_productEntry (primrec_productEntry.comp
    (((hswap.comp hp).pair (Primrec.snd.comp Primrec.fst)).pair Primrec.snd))

private def canonicalDriftEntries (p : ℕ × List ℤ) : Prop :=
  ∀ i < p.1, ∀ j < p.1, entry (p, i, j) = if i = j ∧ i = 0 then 1 else 0

private theorem primrec_canonicalDriftEntries : PrimrecPred canonicalDriftEntries := by
  unfold canonicalDriftEntries
  refine primrec_forall_lt
    (p := fun p : (ℕ × List ℤ) × ℕ => ∀ j < p.1.1,
      entry (p.1, p.2, j) = if p.2 = j ∧ p.2 = 0 then 1 else 0)
    Primrec.fst ?_
  refine primrec_forall_lt
    (p := fun p : ((ℕ × List ℤ) × ℕ) × ℕ =>
      entry (p.1.1, p.1.2, p.2) = if p.1.2 = p.2 ∧ p.1.2 = 0 then 1 else 0)
    (Primrec.fst.comp Primrec.fst) ?_
  have hi : Primrec (fun p : ((ℕ × List ℤ) × ℕ) × ℕ => p.1.2) :=
    Primrec.snd.comp Primrec.fst
  have hEntry : Primrec fun p : ((ℕ × List ℤ) × ℕ) × ℕ =>
      entry (p.1.1, p.1.2, p.2) :=
    primrec_entry.comp ((Primrec.fst.comp Primrec.fst).pair (hi.pair Primrec.snd))
  exact Primrec.eq.comp hEntry
    (Primrec.ite ((Primrec.eq.comp hi Primrec.snd).and (Primrec.eq.comp hi (Primrec.const 0)))
      (Primrec.const 1) (Primrec.const 0))

private theorem sum_range_eq_sum_fin (n : ℕ) (f : ℕ → ℤ) :
    ((List.range n).map f).sum = ∑ i : Fin n, f i.val := by
  rw [← List.sum_toFinset _ (List.nodup_range), List.toFinset_range,
    ← Fin.sum_univ_eq_sum_range]

private theorem commuteEntries_iff (n : ℕ) (a b : List ℤ) :
    commuteEntries (n, a, b) ↔ @Commute (Matrix (Fin n) (Fin n) ℤ) _
      (fun i j : Fin n => entry ((n, a), i, j) : Matrix (Fin n) (Fin n) ℤ)
      (fun i j : Fin n => entry ((n, b), i, j)) := by
  let M (rows : List ℤ) : Matrix (Fin n) (Fin n) ℤ :=
    fun i j => entry ((n, rows), i.val, j.val)
  change (∀ i < n, ∀ j < n,
    productEntry (((n, a, b), i), j) = productEntry (((n, b, a), i), j)) ↔
    M a * M b = M b * M a
  have hmul (x y : List ℤ) (i j : Fin n) :
      (M x * M y) i j = productEntry (((n, x, y), i.val), j.val) := by
    unfold productEntry
    rw [sum_range_eq_sum_fin]
    exact Matrix.mul_apply
  constructor
  · intro h
    apply Matrix.ext
    intro i j
    exact (hmul a b i j).trans ((h i.val i.isLt j.val j.isLt).trans (hmul b a i j).symm)
  · intro h i hi j hj
    have hh := congrArg (fun C : Matrix (Fin n) (Fin n) ℤ => C ⟨i, hi⟩ ⟨j, hj⟩) h
    exact (hmul a b ⟨i, hi⟩ ⟨j, hj⟩).symm.trans (hh.trans (hmul b a ⟨i, hi⟩ ⟨j, hj⟩))

private theorem canonicalDriftEntries_iff (c : IntegerPlantCode) :
    canonicalDriftEntries (c.1, c.2.1) ↔
      c.decode.drift = Matrix.diagonal (fun i => if i.val = 0 then 1 else 0) := by
  unfold canonicalDriftEntries
  have hdiag (i j : Fin c.1) : (Matrix.diagonal (fun k : Fin c.1 => if k.val = 0 then
        (1 : ℤ) else 0)) i j = if i.val = j.val ∧ i.val = 0 then 1 else 0 := by
    by_cases hij : i = j
    · subst j
      simp
    · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
      simp [Matrix.diagonal_apply_ne _ hij, hval]
  constructor
  · intro h
    ext i j
    exact (h i.val i.isLt j.val j.isLt).trans (hdiag i j).symm
  · intro h i hi j hj
    have hx := congrFun (congrFun h ⟨i, hi⟩) ⟨j, hj⟩
    exact hx.trans (hdiag ⟨i, hi⟩ ⟨j, hj⟩)

theorem primrec_canonicalIntegerInstance :
    PrimrecPred CanonicalIntegerInstance := by
  have hcontrols : PrimrecPred fun c : IntegerPlantCode =>
      ∀ a ∈ c.2.2, ∀ b ∈ c.2.2, commuteEntries (c.1, a, b) := by
    have htriples : Primrec fun p : IntegerPlantCode × List ℤ =>
        p.1.2.2.map (fun b => (p.1.1, p.2, b)) :=
      Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
        ((((Primrec.fst.comp Primrec.fst).comp Primrec.fst).pair
          ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))).to₂
    have hinner : PrimrecPred fun p : IntegerPlantCode × List ℤ =>
        ∀ b ∈ p.1.2.2, commuteEntries (p.1.1, p.2, b) :=
      ((PrimrecPred.forall_mem_list primrec_commuteEntries).comp htriples).of_eq
        fun p => by simp
    have hpairs : Primrec fun c : IntegerPlantCode => c.2.2.map (fun a => (c, a)) :=
      Primrec.list_map (Primrec.snd.comp Primrec.snd) Primrec.id.to₂
    exact ((PrimrecPred.forall_mem_list hinner).comp hpairs).of_eq fun c => by simp
  have hdim : PrimrecPred fun c : IntegerPlantCode => 2 ≤ c.1 :=
    Primrec.nat_le.comp (Primrec.const 2) Primrec.fst
  have hdrift : PrimrecPred fun c : IntegerPlantCode =>
      canonicalDriftEntries (c.1, c.2.1) :=
    primrec_canonicalDriftEntries.comp (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))
  refine (primrec_wellFormed.and (hdim.and (hdrift.and hcontrols))).of_eq fun c => ?_
  unfold CanonicalIntegerInstance HasCanonicalDriftAndCommutingControls
  rw [canonicalDriftEntries_iff]
  simp only [decode]
  apply and_congr_right'
  apply and_congr_right'
  apply and_congr_right'
  constructor
  · intro h i j
    exact (commuteEntries_iff c.1 _ _).mp
      (h _ (List.get_mem c.2.2 i) _ (List.get_mem c.2.2 j))
  · intro h a ha b hb
    rcases List.mem_iff_get.mp ha with ⟨i, rfl⟩
    rcases List.mem_iff_get.mp hb with ⟨j, rfl⟩
    exact (commuteEntries_iff c.1 _ _).mpr (h i j)

end PlantCode

theorem inputValidationComputable : Targets.InputValidationComputable := by
  obtain ⟨d, hd⟩ := PlantCode.primrec_canonicalIntegerInstance
  exact ⟨PlantCode.computable_wellFormed, PlantCode.computable_wellFormed, d, hd.to_comp⟩

end ContinuousBilinear
