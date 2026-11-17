import ContinuousBilinear.Targets

namespace ContinuousBilinear

open IntegerPolynomialCode

theorem integerUndecidability_of_reduction (hH10 : Targets.IntegerHilbertTenth)
    (hReduction : Targets.IntegerReduction) : Targets.IntegerUndecidability := by
  obtain ⟨f, hf, h⟩ := hReduction
  have hMany : HasIntegerRoot ≤₀ IntegerGlobalControllability :=
    ⟨f, hf, fun p => (h p).2⟩
  exact fun hd => hH10 (ComputablePred.computable_of_manyOneReducible hMany hd)

/-- A reduction whose outputs satisfy the canonical promise rules out partial
recursive deciders that halt and answer correctly on all promised inputs. -/
theorem canonicalIntegerNoPartrecDecider_of_reduction (hH10 : Targets.IntegerHilbertTenth)
    {P : IntegerPlantCode → Prop}
    (hReduction : ∃ f : IntegerPolynomialCode → IntegerPlantCode, Computable f ∧
      ∀ p, CanonicalIntegerInstance (f p) ∧ (HasIntegerRoot p ↔ P (f p))) :
    ¬ ∃ decide : IntegerPlantCode →. Bool, Partrec decide ∧
      ∀ c, CanonicalIntegerInstance c → ∃ b : Bool, b ∈ decide c ∧ (b = true ↔ P c) := by
  classical
  obtain ⟨f, hf, h⟩ := hReduction
  rintro ⟨decider, hdecider, hcorrect⟩
  have hAnswer (p : IntegerPolynomialCode) :
      ∃ b : Bool, b ∈ decider (f p) ∧ (b = true ↔ HasIntegerRoot p) := by
    obtain ⟨b, hb, heq⟩ := hcorrect (f p) (h p).1
    exact ⟨b, hb, heq.trans (h p).2.symm⟩
  choose answer hmem hiff using hAnswer
  have hComputable : Computable answer := (hdecider.comp hf).of_eq_tot hmem
  let : DecidablePred HasIntegerRoot := fun p =>
    if h : answer p = true then isTrue ((hiff p).mp h)
    else isFalse (fun hp => h ((hiff p).mpr hp))
  apply hH10
  refine ⟨inferInstance, hComputable.of_eq fun p => ?_⟩
  exact Bool.eq_iff_iff.mpr ((hiff p).trans (Iff.of_eq decide_eq_true_eq).symm)

theorem canonicalIntegerUndecidability_of_reduction (hH10 : Targets.IntegerHilbertTenth)
    (hReduction : Targets.IntegerReduction) : Targets.CanonicalIntegerUndecidability := by
  obtain ⟨f, hf, h⟩ := hReduction
  exact canonicalIntegerNoPartrecDecider_of_reduction hH10
    (P := fun c => GloballyControllable (toReal c.decode))
    ⟨f, hf, fun p => ⟨(h p).1, (h p).2.trans
      ⟨And.right, fun hc => ⟨(h p).1.1, hc⟩⟩⟩⟩

theorem canonicalIntegerNoTotalDecider_of_undecidability
    (h : Targets.CanonicalIntegerUndecidability) : Targets.CanonicalIntegerNoTotalDecider := by
  rintro ⟨f, hf, hcorrect⟩
  exact h ⟨(f : IntegerPlantCode →. Bool), hf.partrec,
    fun c hc => ⟨f c, Part.mem_some _, hcorrect c hc⟩⟩

theorem rationalUndecidability_of_integer (hInteger : Targets.IntegerUndecidability)
    (hTransport : Targets.IntegerToRationalTransport) : Targets.RationalUndecidability := by
  have hMany : IntegerGlobalControllability ≤₀ RationalGlobalControllability :=
    ⟨PlantCode.map (fun z : ℤ => (z : ℚ)), hTransport.1, hTransport.2⟩
  exact fun hd => hInteger (ComputablePred.computable_of_manyOneReducible hMany hd)

end ContinuousBilinear
