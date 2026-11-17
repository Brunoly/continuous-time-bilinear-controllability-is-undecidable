import ContinuousBilinear.CompilerRationalTransportProof

namespace ContinuousBilinear

/-- Mapping a computable function over a finite list is computable. -/
theorem computable_list_map {α β γ : Type*} [Primcodable α] [Primcodable β]
    [Primcodable γ] [Inhabited β] {xs : α → List β} {f : α → β → γ}
    (hxs : Computable xs) (hf : Computable₂ f) : Computable fun a => (xs a).map (f a) := by
  have hget : Computable₂ (fun a (i : ℕ) => (xs a)[i]?.getD default) :=
    (Primrec.option_getD.to_comp.comp
      (Primrec.list_getElem?.to_comp.comp (hxs.comp Computable.fst) Computable.snd)
      (Computable.const default)).to₂
  let atIndex (a : α) (k : ℕ) : γ := f a ((xs a)[k]?.getD default)
  have hatIndex : Computable₂ atIndex := hf.comp₂ Primrec₂.left.to_comp hget
  have hrange : Computable₂ (fun a n => (List.range n).map (atIndex a)) := by
    have hnext : Computable₂ (fun (p : α × ℕ) (step : ℕ × List γ) =>
        step.2 ++ [atIndex p.1 step.1]) :=
      (Primrec.list_concat.to_comp.comp (Computable.snd.comp Computable.snd)
        (hatIndex.comp (Computable.fst.comp Computable.fst)
          (Computable.fst.comp Computable.snd))).to₂
    exact (Computable.nat_rec Computable.snd (Computable.const ([] : List γ)) hnext).of_eq
      fun p => by
        rcases p with ⟨a, n⟩
        induction n with
        | zero => rfl
        | succ n ih => simp [List.range_succ, ih]
  refine (hrange.comp Computable.id (Primrec.list_length.to_comp.comp hxs)).of_eq fun a => ?_
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    have hi : i < (xs a).length := by simpa using h₂
    simp [atIndex, hi]

namespace PlantCode

/-- The product of the positive reduced denominators of the entries. -/
def commonDenominator (entries : List ℚ) : ℕ :=
  (entries.map Rat.den).prod

/-- Multiply every entry by the same denominator to get integer entries. -/
def clearDenominators (entries : List ℚ) : List ℤ :=
  entries.map fun q => q.num * ((commonDenominator entries / q.den : ℕ) : ℤ)

@[simp] theorem clearDenominators_length (entries : List ℚ) :
    (clearDenominators entries).length = entries.length := by
  simp [clearDenominators]

theorem commonDenominator_pos (entries : List ℚ) :
    0 < commonDenominator entries := by
  induction entries with
  | nil => simp [commonDenominator]
  | cons q qs ih => exact mul_pos q.den_pos ih

theorem den_dvd_commonDenominator (entries : List ℚ) {q : ℚ} (hq : q ∈ entries) :
    q.den ∣ commonDenominator entries := by
  induction entries with
  | nil => simp at hq
  | cons r rs ih =>
    change q.den ∣ r.den * commonDenominator rs
    rcases List.mem_cons.mp hq with rfl | h
    · exact dvd_mul_right _ _
    · exact dvd_mul_of_dvd_right (ih h) _

theorem cast_clearDenominators_entry (entries : List ℚ) (q : ℚ) (hq : q ∈ entries) :
    ((q.num * ((commonDenominator entries / q.den : ℕ) : ℤ) : ℤ) : ℚ) =
      (commonDenominator entries : ℚ) * q := by
  have hden : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have hm : ((commonDenominator entries / q.den : ℕ) : ℚ) * (q.den : ℚ) =
      (commonDenominator entries : ℚ) := by
    exact_mod_cast Nat.div_mul_cancel (den_dvd_commonDenominator entries hq)
  calc
    _ = ((commonDenominator entries / q.den : ℕ) : ℚ) * q.num := by
      rw [Int.cast_mul, Int.cast_natCast, mul_comm]
    _ = (((commonDenominator entries / q.den : ℕ) : ℚ) * (q.den : ℚ)) * q := by
      conv_rhs => arg 2; rw [← q.num_div_den]
      field_simp [hden]
    _ = _ := by rw [hm]

theorem cast_clearDenominators_getD (entries : List ℚ) (i : ℕ) :
    (((clearDenominators entries).getD i 0 : ℤ) : ℚ) =
      (commonDenominator entries : ℚ) * entries.getD i 0 := by
  simp only [clearDenominators, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : entries[i]? with
  | none => simp
  | some q =>
    simp only [Option.map_some, Option.getD_some]
    exact cast_clearDenominators_entry entries q (List.mem_of_getElem? h)

private theorem primrec_natList_prod : Primrec (fun ns : List ℕ => ns.prod) := by
  have hfold : Primrec (fun ns : List ℕ => ns.foldr (· * ·) 1) :=
    Primrec.list_foldr Primrec.id (Primrec.const 1)
      ((Primrec₂.uncurry.mpr Primrec.nat_mul).comp Primrec.snd).to₂
  refine hfold.of_eq fun ns => ?_
  induction ns with
  | nil => rfl
  | cons n ns ih => simp [ih]

theorem computable_commonDenominator : Computable commonDenominator :=
  primrec_natList_prod.to_comp.comp
    (computable_list_map Computable.id (computable_rat_den.comp Computable.snd).to₂)

theorem computable_clearDenominators : Computable clearDenominators := by
  apply computable_list_map Computable.id
  exact (primrec_int_mul.to_comp.comp (computable_rat_num.comp Computable.snd)
    (primrec_int_ofNat.to_comp.comp (Primrec.nat_div.to_comp.comp
      (computable_commonDenominator.comp Computable.fst)
      (computable_rat_den.comp Computable.snd)))).to₂

end PlantCode
end ContinuousBilinear
