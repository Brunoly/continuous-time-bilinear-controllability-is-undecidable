import ContinuousBilinear.ReductionConsequences
import ContinuousBilinear.CompilerRationalTransportProof

namespace ContinuousBilinear

open IntegerPolynomialCode

/-- Exact controllability defined by an arbitrary state reachability relation. -/
def GloballyControllableFor {n : ℕ} (Reachable : State n → State n → Prop) : Prop :=
  ∀ x y, x ≠ 0 → y ≠ 0 → Reachable x y

theorem globallyControllableFor_mono {n : ℕ} {R S : State n → State n → Prop}
    (h : ∀ x y, R x y → S x y) :
    GloballyControllableFor R → GloballyControllableFor S := by
  intro hR x y hx hy
  exact h x y (hR x y hx hy)

/-- The integer reduction gives the same answers for any intermediate class
of controls, represented by the reachability relations it induces. -/
theorem integerRoot_iff_globallyControllableFor_of_intermediate
    (hReduction : Targets.IntegerReductionWithIntegrableControls)
    (Reachable : (P : Plant ℝ) → State P.dimension → State P.dimension → Prop)
    (hPC : ∀ (P : Plant ℝ) x y,
      (∃ M ∈ transitionMonoid P, M.mulVec x = y) → Reachable P x y)
    (hL1 : ∀ (P : Plant ℝ) x y,
      Reachable P x y → IntegrableControlReachable P x y) :
    ∃ f : IntegerPolynomialCode → IntegerPlantCode, Computable f ∧ ∀ p,
      CanonicalIntegerInstance (f p) ∧
        (p.HasIntegerRoot ↔ GloballyControllableFor (Reachable (toReal (f p).decode))) := by
  obtain ⟨f, hf, h⟩ := hReduction
  refine ⟨f, hf, fun p => ⟨(h p).1, ?_⟩⟩
  constructor
  · intro hp x y hx hy
    exact hPC _ x y (((h p).2.1.mp hp).2 x y hx hy)
  · intro hc
    apply (h p).2.2.mpr
    exact fun x y hx hy => hL1 _ x y (hc x y hx hy)

/-- Any reachability relation between finite piecewise-constant and integrable
control reachability gives an undecidable problem for integer and rational plants. -/
theorem intermediateControlUndecidability_of_reduction
    (hH10 : Targets.IntegerHilbertTenth)
    (hReduction : Targets.IntegerReductionWithIntegrableControls)
    (Reachable : (P : Plant ℝ) → State P.dimension → State P.dimension → Prop)
    (hPC : ∀ (P : Plant ℝ) x y,
      (∃ M ∈ transitionMonoid P, M.mulVec x = y) → Reachable P x y)
    (hL1 : ∀ (P : Plant ℝ) x y,
      Reachable P x y → IntegrableControlReachable P x y) :
    (¬ ComputablePred (fun c : IntegerPlantCode =>
      c.WellFormed ∧ GloballyControllableFor (Reachable (toReal c.decode)))) ∧
    (¬ ComputablePred (fun c : RationalPlantCode =>
      c.WellFormed ∧ GloballyControllableFor (Reachable (toReal c.decode)))) ∧
    (¬ ∃ decide : IntegerPlantCode →. Bool, Partrec decide ∧
      ∀ c, CanonicalIntegerInstance c → ∃ b : Bool, b ∈ decide c ∧
        (b = true ↔ GloballyControllableFor (Reachable (toReal c.decode)))) := by
  obtain ⟨f, hf, h⟩ :=
    integerRoot_iff_globallyControllableFor_of_intermediate hReduction Reachable hPC hL1
  let Pℤ (c : IntegerPlantCode) : Prop :=
    c.WellFormed ∧ GloballyControllableFor (Reachable (toReal c.decode))
  let Pℚ (c : RationalPlantCode) : Prop :=
    c.WellFormed ∧ GloballyControllableFor (Reachable (toReal c.decode))
  have hMany : HasIntegerRoot ≤₀ Pℤ :=
    ⟨f, hf, fun p => (h p).2.trans ⟨fun hc => ⟨(h p).1.1, hc⟩, And.right⟩⟩
  have hInteger : ¬ ComputablePred Pℤ :=
    fun hd => hH10 (ComputablePred.computable_of_manyOneReducible hMany hd)
  have hTransport : Pℤ ≤₀ Pℚ := by
    refine ⟨PlantCode.map (fun z : ℤ => (z : ℚ)), integerToRationalTransport.1, ?_⟩
    intro c
    exact and_congr (PlantCode.wellFormed_map_iff (fun z : ℤ => (z : ℚ)) c).symm
      (Iff.of_eq (congrArg (fun P : Plant ℝ => GloballyControllableFor (Reachable P))
        (toReal_decode_map_intCast c).symm))
  exact ⟨hInteger, (fun hd => hInteger
    (ComputablePred.computable_of_manyOneReducible hTransport hd)),
    canonicalIntegerNoPartrecDecider_of_reduction hH10 ⟨f, hf, h⟩⟩

theorem integrableIntegerUndecidability_of_reduction (hH10 : Targets.IntegerHilbertTenth)
    (hReduction : Targets.IntegerReductionWithIntegrableControls) :
    Targets.IntegrableIntegerUndecidability := by
  obtain ⟨f, hf, h⟩ := hReduction
  have hMany : HasIntegerRoot ≤₀ (fun c : IntegerPlantCode => c.WellFormed ∧
      GloballyControllableWithIntegrableControls (toReal c.decode)) :=
    ⟨f, hf, fun p => (h p).2.2.trans ⟨fun hc => ⟨(h p).1.1, hc⟩, And.right⟩⟩
  exact fun hd => hH10 (ComputablePred.computable_of_manyOneReducible hMany hd)

theorem integrableRationalUndecidability_of_integer
    (hInteger : Targets.IntegrableIntegerUndecidability) :
    Targets.IntegrableRationalUndecidability := by
  have hMany :
      (fun c : IntegerPlantCode => c.WellFormed ∧
        GloballyControllableWithIntegrableControls (toReal c.decode)) ≤₀
      (fun c : RationalPlantCode => c.WellFormed ∧
        GloballyControllableWithIntegrableControls (toReal c.decode)) := by
    refine ⟨PlantCode.map (fun z : ℤ => (z : ℚ)), integerToRationalTransport.1, ?_⟩
    intro c
    simp only [PlantCode.wellFormed_map_iff, toReal_decode_map_intCast]
  exact fun hd => hInteger (ComputablePred.computable_of_manyOneReducible hMany hd)

end ContinuousBilinear
