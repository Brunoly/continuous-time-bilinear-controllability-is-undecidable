import ContinuousBilinear.Targets

namespace ContinuousBilinear

/-- A total relation with a computable certificate test admits a computable choice
function, by searching encoded certificates in increasing order. -/
theorem exists_computable_choice {α β : Type*} [Primcodable α] [Primcodable β]
    {R : α → β → Prop} (hR : ComputablePred fun ab : α × β => R ab.1 ab.2)
    (htotal : ∀ a, ∃ b, R a b) :
    ∃ f : α → β, Computable f ∧ ∀ a, R a (f a) := by
  obtain ⟨d, hd⟩ := hR
  let accept (a : α) (n : ℕ) : Option β :=
    Option.casesOn (Encodable.decode (α := β) n) none fun b =>
      cond (@decide (R a b) (d (a, b))) (some b) none
  have hc : Computable₂ accept := by
    change Computable (fun p : α × ℕ => accept p.1 p.2)
    refine Computable.option_casesOn
      (g := fun (p : α × ℕ) (b : β) =>
        cond (@decide (R p.1 b) (d (p.1, b))) (some b) none)
      (Computable.decode.comp Computable.snd) (Computable.const none) ?_
    have htest : Computable₂ (fun (p : α × ℕ) (b : β) => @decide (R p.1 b) (d (p.1, b))) :=
      (hd.comp ((Computable.fst.comp Computable.fst).pair Computable.snd)).to₂
    exact (Computable.cond (show Computable _ from htest)
      (Computable.option_some.comp Computable.snd) (Computable.const none)).to₂
  let search (a : α) : Part β := Nat.rfindOpt (accept a)
  have hs : Partrec search := Partrec.rfindOpt hc
  have hvalid (a : α) (n : ℕ) (b : β) (hb : b ∈ accept a n) : R a b := by
    unfold accept at hb
    cases hdec : Encodable.decode (α := β) n with
    | none => simp [hdec] at hb
    | some c =>
      by_cases hc' : R a c
      · have heq : c = b := by simpa [hdec, hc'] using hb
        exact heq ▸ hc'
      · simp [hdec, hc'] at hb
  have hdom (a : α) : (search a).Dom := by
    obtain ⟨b, hb⟩ := htotal a
    apply Nat.rfindOpt_dom.mpr
    refine ⟨Encodable.encode b, b, ?_⟩
    simp [accept, hb]
  let choose (a : α) := (search a).get (hdom a)
  have hchoose (a : α) : choose a ∈ search a := Part.get_mem _
  refine ⟨choose, hs.of_eq_tot hchoose, fun a => ?_⟩
  obtain ⟨n, hn⟩ := Nat.rfindOpt_spec (hchoose a)
  exact hvalid a n (choose a) hn

/-- A finite certificate test suffices for the effective plant reduction if each
polynomial has a valid certificate and each accepted certificate yields a correct
canonical plant. -/
theorem integerReduction_of_computable_certificates
    {Certificate : Type*} [Primcodable Certificate]
    {Accept : IntegerPolynomialCode → Certificate → Prop}
    (hAccept : ComputablePred (fun pc : IntegerPolynomialCode × Certificate =>
      Accept pc.1 pc.2))
    (extract : IntegerPolynomialCode → Certificate → IntegerPlantCode)
    (hExtract : Computable₂ extract)
    (hExists : ∀ p, ∃ c, Accept p c)
    (hCorrect : ∀ p c, Accept p c →
      CanonicalIntegerInstance (extract p c) ∧
        (p.HasIntegerRoot ↔ IntegerGlobalControllability (extract p c))) :
    Targets.IntegerReduction := by
  obtain ⟨certificate, hc, hcert⟩ := exists_computable_choice hAccept hExists
  exact ⟨fun p => extract p (certificate p), hExtract.comp Computable.id hc,
    fun p => hCorrect p (certificate p) (hcert p)⟩

end ContinuousBilinear
