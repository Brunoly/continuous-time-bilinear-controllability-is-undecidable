import ContinuousBilinear.Encoding

namespace ContinuousBilinear

open Encodable

private theorem encode_int_ofNat (n : ℕ) : encode (Int.ofNat n) = Nat.bit false n := rfl

private theorem encode_int_negSucc (n : ℕ) : encode (Int.negSucc n) = Nat.bit true n := rfl

theorem primrec_int_ofNat : Primrec Int.ofNat :=
  Primrec.encode_iff.mp (Primrec.nat_double.of_eq fun n => (encode_int_ofNat n).symm)

theorem primrec_int_negSucc : Primrec Int.negSucc :=
  Primrec.encode_iff.mp (Primrec.nat_double_succ.of_eq fun n => (encode_int_negSucc n).symm)

theorem primrec_int_subNatNat : Primrec₂ Int.subNatNat := by
  apply Primrec₂.curry.mp
  have hdiff : Primrec (fun p : ℕ × ℕ => p.2 - p.1) :=
    Primrec.nat_sub.comp Primrec.snd Primrec.fst
  refine (Primrec.ite (Primrec.eq.comp hdiff (Primrec.const 0))
    (primrec_int_ofNat.comp (Primrec.nat_sub.comp Primrec.fst Primrec.snd))
    (primrec_int_negSucc.comp (Primrec.pred.comp hdiff))).of_eq ?_
  intro p
  unfold Function.curry Int.subNatNat
  cases h : p.2 - p.1 <;> simp [h]

private def intPositive (z : ℤ) : ℕ :=
  if (encode z).bodd = true then 0 else (encode z).div2

private def intNegative (z : ℤ) : ℕ :=
  if (encode z).bodd = true then (encode z).div2 + 1 else 0

private theorem primrec_intPositive : Primrec intPositive :=
  Primrec.ite (Primrec.eq.comp (Primrec.nat_bodd.comp Primrec.encode) (Primrec.const true))
    (Primrec.const 0) (Primrec.nat_div2.comp Primrec.encode)

private theorem primrec_intNegative : Primrec intNegative :=
  Primrec.ite (Primrec.eq.comp (Primrec.nat_bodd.comp Primrec.encode) (Primrec.const true))
    (Primrec.succ.comp (Primrec.nat_div2.comp Primrec.encode)) (Primrec.const 0)

private theorem int_eq_pos_sub_neg (z : ℤ) : (intPositive z : ℤ) - (intNegative z : ℤ) = z := by
  cases z with
  | ofNat n =>
    simp only [intPositive, intNegative, encode_int_ofNat, Nat.bodd_bit, Nat.div2_bit]
    simp
  | negSucc n =>
    simp only [intPositive, intNegative, encode_int_negSucc, Nat.bodd_bit, Nat.div2_bit]
    simp only [ite_true]
    omega

theorem primrec_int_natAbs : Primrec Int.natAbs :=
  (Primrec.nat_add.comp primrec_intPositive primrec_intNegative).of_eq fun z => by
    cases z with
    | ofNat n =>
      simp only [intPositive, intNegative, encode_int_ofNat, Nat.bodd_bit, Nat.div2_bit]
      simp
    | negSucc n =>
      simp only [intPositive, intNegative, encode_int_negSucc, Nat.bodd_bit, Nat.div2_bit]
      simp

theorem primrec_int_add : Primrec₂ ((· + ·) : ℤ → ℤ → ℤ) := by
  apply Primrec₂.curry.mp
  refine (primrec_int_subNatNat.comp
    (Primrec.nat_add.comp (primrec_intPositive.comp Primrec.fst)
      (primrec_intPositive.comp Primrec.snd))
    (Primrec.nat_add.comp (primrec_intNegative.comp Primrec.fst)
      (primrec_intNegative.comp Primrec.snd))).of_eq ?_
  intro p
  change _ = p.1 + p.2
  rw [Int.subNatNat_eq_coe, Int.natCast_add, Int.natCast_add]
  calc
    _ = ((intPositive p.1 : ℤ) - intNegative p.1) +
        ((intPositive p.2 : ℤ) - intNegative p.2) := by ring
    _ = _ := by rw [int_eq_pos_sub_neg, int_eq_pos_sub_neg]

theorem primrec_int_mul : Primrec₂ ((· * ·) : ℤ → ℤ → ℤ) := by
  apply Primrec₂.curry.mp
  let p₁ := primrec_intPositive.comp (Primrec.fst : Primrec (Prod.fst : ℤ × ℤ → ℤ))
  let n₁ := primrec_intNegative.comp (Primrec.fst : Primrec (Prod.fst : ℤ × ℤ → ℤ))
  let p₂ := primrec_intPositive.comp (Primrec.snd : Primrec (Prod.snd : ℤ × ℤ → ℤ))
  let n₂ := primrec_intNegative.comp (Primrec.snd : Primrec (Prod.snd : ℤ × ℤ → ℤ))
  refine (primrec_int_subNatNat.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp p₁ p₂) (Primrec.nat_mul.comp n₁ n₂))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp p₁ n₂) (Primrec.nat_mul.comp n₁ p₂))).of_eq ?_
  intro p
  change _ = p.1 * p.2
  rw [Int.subNatNat_eq_coe, Int.natCast_add, Int.natCast_add]
  push_cast
  calc
    _ = ((intPositive p.1 : ℤ) - intNegative p.1) *
        ((intPositive p.2 : ℤ) - intNegative p.2) := by ring
    _ = _ := by rw [int_eq_pos_sub_neg, int_eq_pos_sub_neg]

end ContinuousBilinear
