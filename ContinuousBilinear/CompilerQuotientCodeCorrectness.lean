import ContinuousBilinear.CompilerQuotientCode
import ContinuousBilinear.CompilerQuotientCoordinates
import ContinuousBilinear.CompilerMinimalEncodingProof

namespace ContinuousBilinear.RationalFeedbackCode.QuotientCoordinateData

open PolynomialLift Module PlantCode

noncomputable section

/-- Matrix interpretation of the inverse observation table stored by rows. -/
def inverseMatrix (p : QuotientCoordinateData) :
    Matrix (Fin p.dimension) (Fin p.dimension) ℚ :=
  Matrix.of fun i j => p.inverseEntry i.val j.val

private theorem wordCoordinate_eq
    (p : QuotientCoordinateData)
    (u v : Fin p.dimension → List (Fin p.1.2.2.2.length))
    (hRow : ∀ i, p.2.1.getD i.val [] = (u i).map Fin.val)
    (B : Basis (Fin p.dimension) ℚ
      (p.1.representation.reachable ⧸ p.1.representation.unobservable))
    (hB : ∀ j, B j = p.1.representation.minimalRepresentation.wordAction (v j)
      p.1.representation.minimalRepresentation.initial)
    (hR : p.inverseMatrix * p.1.representation.wordHankel u v = 1)
    (i : Fin p.dimension) (w : List (Fin p.1.2.2.2.length)) :
    p.wordCoordinate i.val (w.map Fin.val) = B.equivFun
      (p.1.representation.minimalRepresentation.wordAction w
        p.1.representation.minimalRepresentation.initial) i := by
  let F := p.1.representation
  let G := F.minimalRepresentation
  have hHG : G.wordHankel u v = F.wordHankel u v := by
    ext j k
    exact F.minimal_output_word (u j ++ v k)
  have hR' : p.inverseMatrix * G.wordHankel u v = 1 := by rwa [hHG]
  rw [G.equivFun_eq_inverseHankel_mulVec u v B hB p.inverseMatrix hR',
    G.wordObservationMap_word]
  unfold wordCoordinate
  rw [← List.sum_toFinset _ (List.nodup_range), List.toFinset_range,
    ← Fin.sum_univ_eq_sum_range]
  change (∑ j : Fin p.dimension,
    p.inverseEntry i.val j.val * p.1.wordOutput (p.2.1.getD j.val [] ++ w.map Fin.val)) =
    ∑ j : Fin p.dimension, p.inverseEntry i.val j.val *
      G.output (G.wordAction (u j ++ w) G.initial)
  apply Finset.sum_congr rfl
  intro j _
  rw [hRow j, ← List.map_append, p.1.wordOutput_eq, F.minimal_output_word]

/-- The matrices and vectors obtained from the selected observation equations
are precisely the quotient operators in the selected reachable-state basis. -/
theorem quotientCode_eq_encodeRepresentation
    (p : QuotientCoordinateData)
    (u v : Fin p.dimension → List (Fin p.1.2.2.2.length))
    (hRow : ∀ i, p.2.1.getD i.val [] = (u i).map Fin.val)
    (hCol : ∀ i, p.2.2.1.getD i.val [] = (v i).map Fin.val)
    (B : Basis (Fin p.dimension) ℚ
      (p.1.representation.reachable ⧸ p.1.representation.unobservable))
    (hB : ∀ j, B j = p.1.representation.minimalRepresentation.wordAction (v j)
      p.1.representation.minimalRepresentation.initial)
    (hR : p.inverseMatrix * p.1.representation.wordHankel u v = 1) :
    p.quotientCode = encodeRepresentation p.1.representation.minimalRepresentation B := by
  let F := p.1.representation
  let G := F.minimalRepresentation
  have hInit : (List.range p.dimension).map (fun i => p.wordCoordinate i []) =
      List.ofFn (B.equivFun G.initial) := by
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      have hi : i < p.dimension := by simpa using h₂
      simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
      exact wordCoordinate_eq p u v hRow B hB hR ⟨i, hi⟩ []
  have hOut : p.2.2.1.map p.1.wordOutput = List.ofFn (fun j => G.output (B j)) := by
    apply List.ext_getElem
    · simp [dimension]
    · intro i h₁ h₂
      have hi : i < p.dimension := by simpa using h₂
      have hj : i < p.2.2.1.length := hi
      have hw : p.2.2.1[i] = (v ⟨i, hi⟩).map Fin.val := by
        simpa only [List.getD_eq_getElem?_getD, getElem?_pos p.2.2.1 i hj, Option.getD_some]
          using hCol ⟨i, hi⟩
      simp only [List.getElem_map, List.getElem_ofFn]
      rw [hw, wordOutput_eq, hB]
      exact (F.minimal_output_word (v ⟨i, hi⟩)).symm
  let P : Plant ℚ := ⟨p.dimension, p.1.2.2.2.length, 0, G.coordinateOperators B⟩
  have hK (k : Fin P.controls) (i j : Fin P.dimension) :
      p.operatorEntry k.val i.val j.val = P.control k i j := by
    unfold operatorEntry
    rw [hCol j]
    change p.wordCoordinate i.val ((k :: v j).map Fin.val) =
      G.coordinateOperators B k i j
    rw [wordCoordinate_eq p u v hRow B hB hR i (k :: v j)]
    change B.repr (G.operator k (G.wordAction (v j) G.initial)) i = _
    rw [← hB j]
    exact (LinearMap.toMatrix_apply B B (G.operator k) i j).symm
  have hControls := congrArg (fun c : RationalPlantCode => c.2.2)
    (tabulatePlant_eq_encode P (fun _ _ => (0 : ℚ)) p.operatorEntry (fun _ _ => rfl) hK)
  change (tabulatePlant p.dimension p.1.2.2.2.length (fun _ _ => 0) p.operatorEntry).2.2 =
    List.ofFn (fun k => matrixEntries (G.coordinateOperators B k)) at hControls
  unfold quotientCode encodeRepresentation
  rw [hInit, hOut, hControls]

/-- The computed code is the minimal quotient if the elimination leaves zero
residual on the bounded observation table. -/
theorem quotientCode_correct
    (p : QuotientCoordinateData)
    (u v : Fin p.dimension → List (Fin p.1.2.2.2.length))
    (hRow : ∀ i, p.2.1.getD i.val [] = (u i).map Fin.val)
    (hCol : ∀ i, p.2.2.1.getD i.val [] = (v i).map Fin.val)
    (hH : p.1.representation.wordHankel u v * p.inverseMatrix = 1)
    (hR : p.inverseMatrix * p.1.representation.wordHankel u v = 1)
    (hResidual : ∀ a b : List (Fin p.1.2.2.2.length), a.length ≤ p.1.1 → b.length ≤ p.1.1 →
      p.1.representation.output (p.1.representation.wordAction (a ++ b) p.1.representation.initial) =
        ∑ j, p.1.representation.output
          (p.1.representation.wordAction (a ++ v j) p.1.representation.initial) *
            (p.inverseMatrix.mulVec (p.1.representation.wordObservations u b)) j)
    (hcomm : ∀ i j, Commute (p.1.operator i) (p.1.operator j)) :
    wordOutputsAgree (p.1, p.quotientCode) ∧
      (∀ i j, Commute (p.quotientCode.operator i) (p.quotientCode.operator j)) ∧
      p.quotientCode.representation.reachable = ⊤ ∧
      Submodule.span ℚ (Set.range fun w => p.quotientCode.representation.output.comp
        (p.quotientCode.representation.wordAction w)) = ⊤ := by
  have hDim : Module.finrank ℚ (Fin p.1.1 → ℚ) ≤ p.1.1 := by simp
  obtain ⟨B, hB⟩ := p.1.representation.exists_quotientBasis_of_schurComplement_eq_zero
    u v p.inverseMatrix hH hR hDim hResidual
  rw [quotientCode_eq_encodeRepresentation p u v hRow hCol B hB hR]
  exact encodeMinimalRepresentation_correct p.1 B hcomm

end

end ContinuousBilinear.RationalFeedbackCode.QuotientCoordinateData
