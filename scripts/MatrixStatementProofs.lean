import scripts.VerifyUndecidability

namespace ContinuousBilinear

private theorem encode_decode_of_wellFormed {K : Type*} [Zero K]
    (c : PlantCode K) (hc : c.WellFormed) : PlantCode.encode c.decode = c := by
  change (c.1, PlantCode.matrixEntries c.decode.drift,
    List.ofFn (fun i => PlantCode.matrixEntries (c.decode.control i))) = c
  have hA : PlantCode.matrixEntries c.decode.drift = c.2.1 :=
    PlantCode.matrixEntries_getD_roundtrip _ _ hc.1
  rw [hA]
  congr 2
  apply List.ext_getElem
  · simp [PlantCode.decode]
  · intro i _ hi
    simp only [List.getElem_ofFn]
    exact PlantCode.matrixEntries_getD_roundtrip _ _
      (hc.2 _ (List.get_mem _ ⟨i, hi⟩))

theorem rationalMatrixUndecidability :
    ¬ ∃ decide : RationalPlantCode → Bool, Computable decide ∧
      ∀ P : Plant ℚ, decide (PlantCode.encode P) = true ↔ GloballyControllable (toReal P) := by
  rintro ⟨f, hf, hcorrect⟩
  obtain ⟨valid, hv⟩ := PlantCode.computable_wellFormed (R := ℚ)
  let := valid
  let test (c : RationalPlantCode) := decide c.WellFormed && f c
  have htest : Computable test := Primrec.and.to_comp.comp hv hf
  apply rationalUndecidability
  apply (ComputablePred.computable_iff.mpr ⟨test, htest, rfl⟩).of_eq
  intro c
  change test c = true ↔ c.WellFormed ∧ GloballyControllable (toReal c.decode)
  simp only [test, Bool.and_eq_true, decide_eq_true_eq]
  refine and_congr_right fun hc => ?_
  simpa only [encode_decode_of_wellFormed c hc] using hcorrect c.decode

theorem canonicalIntegerMatrixUndecidability :
    ¬ ∃ decide : IntegerPlantCode →. Bool, Partrec decide ∧
      ∀ P : Plant ℤ, HasCanonicalDriftAndCommutingControls P →
        ∃ b : Bool, b ∈ decide (PlantCode.encode P) ∧
          (b = true ↔ GloballyControllable (toReal P)) := by
  rintro ⟨decide, hcomp, hcorrect⟩
  apply canonicalIntegerUndecidability
  refine ⟨decide, hcomp, fun c hc => ?_⟩
  simpa only [encode_decode_of_wellFormed c hc.1] using hcorrect c.decode hc.2

end ContinuousBilinear
