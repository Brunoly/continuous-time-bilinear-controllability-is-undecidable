import ContinuousBilinear.CompilerRationalTransportProof

namespace ContinuousBilinear

theorem computablePred_eq {α β : Type*} [Primcodable α] [Primcodable β]
    {f g : α → β} (hf : Computable f) (hg : Computable g) :
    ComputablePred (fun a => f a = g a) := by
  classical
  exact (Primrec.eq.decide.to_comp.comp hf hg).computablePred

theorem computable_cond_of_computablePred {α β : Type*}
    [Primcodable α] [Primcodable β] {p : α → Prop} [DecidablePred p] {f g : α → β}
    (hp : ComputablePred p) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => if p a then f a else g a) := by
  simpa [Bool.cond_decide] using Computable.cond hp.decide hf hg

private theorem computable_int_natCast : Computable (fun n : ℕ => (n : ℤ)) :=
  primrec_int_ofNat.to_comp

set_option maxHeartbeats 1000000 in
/-- Normalizing an integer numerator and denominator is computable in the
denumerable rational encoding. -/
theorem computable_rat_divInt : Computable₂ Rat.divInt := by
  let R (ab : ℤ × ℤ) (q : ℚ) : Prop :=
    if ab.2 = 0 then q = 0 else q.num * ab.2 = ab.1 * (q.den : ℤ)
  have hc : ComputablePred fun p : (ℤ × ℤ) × ℚ => R p.1 p.2 := by
    have hz : ComputablePred (fun p : (ℤ × ℤ) × ℚ => p.1.2 = 0) :=
      computablePred_eq (Computable.snd.comp Computable.fst) (Computable.const 0)
    have h0 : ComputablePred (fun p : (ℤ × ℤ) × ℚ => p.2 = 0) :=
      computablePred_eq Computable.snd (Computable.const 0)
    have hcross : ComputablePred (fun p : (ℤ × ℤ) × ℚ =>
        p.2.num * p.1.2 = p.1.1 * (p.2.den : ℤ)) :=
      computablePred_eq
        (primrec_int_mul.to_comp.comp (computable_rat_num.comp Computable.snd)
          (Computable.snd.comp Computable.fst))
        (primrec_int_mul.to_comp.comp (Computable.fst.comp Computable.fst)
          ((computable_int_natCast.comp computable_rat_den).comp Computable.snd))
    let accept (p : (ℤ × ℤ) × ℚ) : Bool :=
      if p.1.2 = 0 then decide (p.2 = 0)
      else decide (p.2.num * p.1.2 = p.1.1 * (p.2.den : ℤ))
    have h : Computable accept :=
      computable_cond_of_computablePred hz h0.decide hcross.decide
    exact (ComputablePred.computable_iff.mpr ⟨accept, h, rfl⟩).of_eq fun p => by
      by_cases hz' : p.1.2 = 0 <;> simp [R, accept, hz']
  have hR (ab : ℤ × ℤ) (q : ℚ) : R ab q ↔ q = Rat.divInt ab.1 ab.2 := by
    by_cases hz : ab.2 = 0
    · simp [R, hz]
    · simp only [R, hz, ite_false]
      conv_rhs => lhs; rw [← Rat.num_divInt_den q]
      exact (Rat.divInt_eq_divInt_iff (by exact_mod_cast q.den_nz) hz).symm
  obtain ⟨f, hf, hfR⟩ := exists_computable_choice hc
    (fun ab => ⟨Rat.divInt ab.1 ab.2, (hR _ _).mpr rfl⟩)
  exact hf.of_eq fun ab => (hR _ _).mp (hfR ab)

theorem computable_rat_add : Computable₂ ((· + ·) : ℚ → ℚ → ℚ) := by
  let num₁ := computable_rat_num.comp (Computable.fst : Computable (Prod.fst : ℚ × ℚ → ℚ))
  let num₂ := computable_rat_num.comp (Computable.snd : Computable (Prod.snd : ℚ × ℚ → ℚ))
  let den₁ := (computable_int_natCast.comp computable_rat_den).comp
    (Computable.fst : Computable (Prod.fst : ℚ × ℚ → ℚ))
  let den₂ := (computable_int_natCast.comp computable_rat_den).comp
    (Computable.snd : Computable (Prod.snd : ℚ × ℚ → ℚ))
  refine (computable_rat_divInt.comp (primrec_int_add.to_comp.comp
    (primrec_int_mul.to_comp.comp num₁ den₂) (primrec_int_mul.to_comp.comp num₂ den₁))
    (primrec_int_mul.to_comp.comp den₁ den₂)).of_eq ?_
  intro p
  change Rat.divInt (p.1.num * (p.2.den : ℤ) + p.2.num * (p.1.den : ℤ))
    ((p.1.den : ℤ) * (p.2.den : ℤ)) = p.1 + p.2
  rw [Rat.add_def', Rat.mkRat_eq_divInt, Nat.cast_mul]

theorem computable_rat_mul : Computable₂ ((· * ·) : ℚ → ℚ → ℚ) := by
  let num₁ := computable_rat_num.comp (Computable.fst : Computable (Prod.fst : ℚ × ℚ → ℚ))
  let num₂ := computable_rat_num.comp (Computable.snd : Computable (Prod.snd : ℚ × ℚ → ℚ))
  let den₁ := (computable_int_natCast.comp computable_rat_den).comp
    (Computable.fst : Computable (Prod.fst : ℚ × ℚ → ℚ))
  let den₂ := (computable_int_natCast.comp computable_rat_den).comp
    (Computable.snd : Computable (Prod.snd : ℚ × ℚ → ℚ))
  refine (computable_rat_divInt.comp (primrec_int_mul.to_comp.comp num₁ num₂)
    (primrec_int_mul.to_comp.comp den₁ den₂)).of_eq ?_
  intro p
  change Rat.divInt (p.1.num * p.2.num) ((p.1.den : ℤ) * (p.2.den : ℤ)) = p.1 * p.2
  rw [Rat.mul_def', Rat.mkRat_eq_divInt, Nat.cast_mul]

theorem computable_rat_inv : Computable (Inv.inv : ℚ → ℚ) := by
  refine (computable_rat_divInt.comp (computable_int_natCast.comp computable_rat_den)
    computable_rat_num).of_eq ?_
  intro q
  rw [Rat.inv_def]

theorem computable_rat_div : Computable₂ ((· / ·) : ℚ → ℚ → ℚ) := by
  change Computable (fun p : ℚ × ℚ => p.1 / p.2)
  simpa only [div_eq_mul_inv] using
    computable_rat_mul.comp Computable.fst (computable_rat_inv.comp Computable.snd)

theorem computable_rat_neg : Computable (Neg.neg : ℚ → ℚ) := by
  have hneg : Computable fun z : ℤ => -z :=
    (primrec_int_mul.to_comp.comp (Computable.const (-1)) Computable.id).of_eq
      fun z => neg_one_mul z
  refine (computable_rat_divInt.comp (hneg.comp computable_rat_num)
    (computable_int_natCast.comp computable_rat_den)).of_eq ?_
  intro q
  exact (Rat.neg_def q).symm

theorem computable_rat_sub : Computable₂ ((· - ·) : ℚ → ℚ → ℚ) := by
  change Computable fun p : ℚ × ℚ => p.1 - p.2
  simpa only [sub_eq_add_neg] using
    computable_rat_add.comp Computable.fst (computable_rat_neg.comp Computable.snd)

end ContinuousBilinear
