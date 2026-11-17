import ContinuousBilinear.EncodingProof
import ContinuousBilinear.CompilerCertificateSearchProof
import ContinuousBilinear.CompilerIntegerArithmeticProof

namespace ContinuousBilinear

open Encodable

private abbrev rawRatEncode (r : ℚ) : ℕ := @encode ℚ Rat.instEncodable r

local instance : DecidablePred (· ∈ Set.range rawRatEncode) :=
  @Encodable.decidableRangeEncode ℚ Rat.instEncodable

private theorem rawRatEncode_eq (r : ℚ) : rawRatEncode r = Nat.pair (encode r.num) r.den := by
  cases r
  rfl

private theorem mem_range_rawRatEncode_iff (i : ℕ) :
    i ∈ Set.range rawRatEncode ↔
      0 < i.unpair.2 ∧ (Denumerable.ofNat ℤ i.unpair.1).natAbs.Coprime i.unpair.2 := by
  constructor
  · rintro ⟨r, rfl⟩
    rw [rawRatEncode_eq, Nat.unpair_pair, Denumerable.ofNat_encode]
    exact ⟨Nat.pos_of_ne_zero r.den_nz, r.reduced⟩
  · rintro ⟨hd, hr⟩
    let r : ℚ := ⟨Denumerable.ofNat ℤ i.unpair.1, i.unpair.2, Nat.ne_of_gt hd, hr⟩
    refine ⟨r, ?_⟩
    rw [rawRatEncode_eq]
    change Nat.pair (encode (Denumerable.ofNat ℤ i.unpair.1)) i.unpair.2 = i
    rw [Denumerable.encode_ofNat, Nat.pair_unpair]

private theorem primrec_rawRatRange : PrimrecPred (· ∈ Set.range rawRatEncode) := by
  let numerator : ℕ → ℕ := fun i => (Denumerable.ofNat ℤ i.unpair.1).natAbs
  let denominator : ℕ → ℕ := fun i => i.unpair.2
  have hnum : Primrec numerator := primrec_int_natAbs.comp
    ((Primrec.ofNat ℤ).comp (Primrec.fst.comp Primrec.unpair))
  have hden : Primrec denominator := Primrec.snd.comp Primrec.unpair
  have hpos : PrimrecPred fun i => 0 < denominator i :=
    Primrec.nat_lt.comp (Primrec.const 0) hden
  have hdiv : PrimrecRel ((· ∣ ·) : ℕ → ℕ → Prop) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd Primrec.fst) (Primrec.const 0)).of_eq
      fun p => Nat.dvd_iff_mod_eq_zero.symm
  have htest : PrimrecPred fun p : ℕ × ℕ =>
      p.2 ∣ numerator p.1 ∧ p.2 ∣ denominator p.1 → p.2 = 1 := by
    have hdvd := (hdiv.comp Primrec.snd (hnum.comp Primrec.fst)).and
      (hdiv.comp Primrec.snd (hden.comp Primrec.fst))
    have hOne : PrimrecPred fun p : ℕ × ℕ => p.2 = 1 :=
      Primrec.eq.comp Primrec.snd (Primrec.const 1)
    exact (hdvd.not.or hOne).of_eq fun _ => by tauto
  have hbounded : PrimrecPred fun i =>
      ∀ j < denominator i + 1, j ∣ numerator i ∧ j ∣ denominator i → j = 1 := by
    have hlist : Primrec fun i => (List.range (denominator i + 1)).map (fun j => (i, j)) :=
      Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp hden)) Primrec.id.to₂
    exact ((PrimrecPred.forall_mem_list htest).comp hlist).of_eq fun _ => by simp
  refine (hpos.and hbounded).of_eq fun i => ?_
  rw [mem_range_rawRatEncode_iff]
  change (0 < denominator i ∧ (∀ j < denominator i + 1,
      j ∣ numerator i ∧ j ∣ denominator i → j = 1)) ↔
    (0 < denominator i ∧ (numerator i).Coprime (denominator i))
  apply and_congr_right
  intro hd
  constructor
  · intro h
    rw [Nat.coprime_iff_gcd_eq_one]
    exact h _ (Nat.lt_succ_of_le (Nat.le_of_dvd hd (Nat.gcd_dvd_right _ _)))
      ⟨Nat.gcd_dvd_left _ _, Nat.gcd_dvd_right _ _⟩
  · intro hc _ _ h
    exact Nat.eq_one_of_dvd_coprimes hc h.1 h.2

private def rawRatRank (n : ℕ) : ℕ :=
  ((List.range n).filter fun i => decide (i ∈ Set.range rawRatEncode)).length

private theorem primrec_rawRatRank : Primrec rawRatRank :=
  Primrec.list_length.comp ((Primrec.listFilter primrec_rawRatRange).comp Primrec.list_range)

/-- The denumerable rational code is the rank of the raw numerator/denominator code. -/
private theorem rat_encode_eq_rank (r : ℚ) :
    @encode ℚ Rat.instDenumerable.toEncodable r = rawRatRank (rawRatEncode r) := by
  change ((List.range (rawRatEncode r)).countP fun n =>
    decide (n ∈ Set.range rawRatEncode)) = _
  rw [List.countP_eq_length_filter]
  rfl

theorem primrec_rat_intCast : Primrec (fun z : ℤ => (z : ℚ)) := by
  apply Primrec.encode_iff.mp
  have hpair : Primrec fun z : ℤ => Nat.pair (encode z) 1 :=
    Primrec₂.natPair.comp Primrec.encode (Primrec.const 1)
  refine (primrec_rawRatRank.comp hpair).of_eq fun z => ?_
  rw [rat_encode_eq_rank, rawRatEncode_eq]
  simp

private theorem computable_rawRatEncode : Computable rawRatEncode := by
  let accept (r : ℚ) (n : ℕ) : Prop := n ∈ Set.range rawRatEncode ∧
    rawRatRank n = @encode ℚ Rat.instDenumerable.toEncodable r
  have hcheck : PrimrecPred (fun rn : ℚ × ℕ => accept rn.1 rn.2) :=
    (primrec_rawRatRange.comp Primrec.snd).and
      (Primrec.eq.comp (primrec_rawRatRank.comp Primrec.snd)
        (Primrec.encode.comp Primrec.fst))
  have hcheck' : ComputablePred (fun rn : ℚ × ℕ => accept rn.1 rn.2) := by
    obtain ⟨dec, h⟩ := hcheck
    exact ⟨dec, h.to_comp⟩
  have hex (r : ℚ) : ∃ n, accept r n :=
    ⟨rawRatEncode r, ⟨r, rfl⟩, (rat_encode_eq_rank r).symm⟩
  obtain ⟨f, hf, h⟩ := exists_computable_choice hcheck' hex
  refine hf.of_eq fun r => ?_
  obtain ⟨⟨q, hq⟩, heq⟩ := h r
  have hqe : @encode ℚ Rat.instDenumerable.toEncodable q =
      @encode ℚ Rat.instDenumerable.toEncodable r := by
    rw [rat_encode_eq_rank q, hq, heq]
  have hqr : q = r := @Encodable.encode_injective ℚ Rat.instDenumerable.toEncodable q r hqe
  simpa only [hqr] using hq.symm

theorem computable_rat_num : Computable Rat.num := by
  refine ((Computable.ofNat ℤ).comp (Primrec.fst.to_comp.comp
    (Primrec.unpair.to_comp.comp computable_rawRatEncode))).of_eq fun r => ?_
  rw [rawRatEncode_eq, Nat.unpair_pair, Denumerable.ofNat_encode]

theorem computable_rat_den : Computable Rat.den := by
  refine (Primrec.snd.to_comp.comp
    (Primrec.unpair.to_comp.comp computable_rawRatEncode)).of_eq fun r => ?_
  rw [rawRatEncode_eq, Nat.unpair_pair]

private theorem primrec_mapPlantCode {R S : Type*} [Primcodable R] [Primcodable S]
    {f : R → S} (hf : Primrec f) : Primrec (PlantCode.map f) := by
  have hmap : Primrec (List.map f) :=
    Primrec.list_map Primrec.id (hf.comp Primrec.snd).to₂
  have hmaps : Primrec (List.map (List.map f)) :=
    Primrec.list_map Primrec.id (hmap.comp Primrec.snd).to₂
  exact Primrec.fst.pair ((hmap.comp (Primrec.fst.comp Primrec.snd)).pair
    (hmaps.comp (Primrec.snd.comp Primrec.snd)))

theorem integerToRationalTransport : Targets.IntegerToRationalTransport :=
  ⟨(primrec_mapPlantCode primrec_rat_intCast).to_comp, integerGlobalControllability_iff_rational⟩

end ContinuousBilinear
