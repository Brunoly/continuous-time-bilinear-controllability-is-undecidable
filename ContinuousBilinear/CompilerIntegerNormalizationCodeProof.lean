import ContinuousBilinear.CompilerIntegerPlantProof
import ContinuousBilinear.CompilerPlantTabulationProof

namespace ContinuousBilinear
namespace PlantCode

/-- Clear every control denominator in a well-formed rational plant code with
canonical drift, keeping the drift canonical in the integer code. -/
def clearControlCode (c : RationalPlantCode) : IntegerPlantCode :=
  (c.1, tabulateMatrix c.1 (fun i j => if i = j ∧ i = 0 then 1 else 0),
    c.2.2.map clearDenominators)

theorem computable_clearControlCode : Computable clearControlCode := by
  have hentry : Primrec (fun p : RationalPlantCode × ℕ × ℕ =>
      if p.2.1 = p.2.2 ∧ p.2.1 = 0 then (1 : ℤ) else 0) :=
    Primrec.ite ((Primrec.eq.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).and
        (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0)))
      (Primrec.const 1) (Primrec.const 0)
  exact Computable.fst.pair ((computable_tabulateMatrix Computable.fst hentry.to_comp).pair
    (computable_list_map (Computable.snd.comp Computable.snd)
      (computable_clearDenominators.comp Computable.snd).to₂))

theorem matrixEntries_getD_roundtrip {R : Type*} [Zero R] (n : ℕ)
    (l : List R) (hlen : l.length = n * n) :
    matrixEntries (fun i j : Fin n => l.getD (i.val * n + j.val) 0 :
      Matrix (Fin n) (Fin n) R) = l := by
  apply List.ext_getElem
  · exact (matrixEntries_length _).trans hlen.symm
  · intro k h₁ h₂
    have hk : k < n * n := hlen ▸ h₂
    let u : Fin (n * n) := ⟨k, hk⟩
    let ij := finProdFinEquiv.symm u
    have heq : ij.1.val * n + ij.2.val = k := by
      have hh := congrArg Fin.val (finProdFinEquiv.apply_symm_apply u)
      change ij.2.val + n * ij.1.val = k at hh
      rw [← hh]
      ac_rfl
    change (matrixEntries (fun i j : Fin n => l.getD (i.val * n + j.val) 0 :
      Matrix (Fin n) (Fin n) R))[k]'h₁ = l[k]'h₂
    simp only [matrixEntries, List.getElem_ofFn]
    change l.getD (ij.1.val * n + ij.2.val) 0 = l[k]
    rw [heq, List.getD_eq_getElem?_getD]
    simp [h₂]

theorem clearControlCode_eq_encode (c : RationalPlantCode) (hc : c.WellFormed) :
    clearControlCode c = encode c.decode.clearControlDenominators := by
  have hA : tabulateMatrix c.1 (fun i j => if i = j ∧ i = 0 then (1 : ℤ) else 0) =
      matrixEntries (Matrix.diagonal (fun i : Fin c.1 => if i.val = 0 then 1 else 0)) := by
    apply tabulateMatrix_eq_matrixEntries
    intro i j
    by_cases hij : i = j
    · subst j
      simp
    · have hn : i.val ≠ j.val := fun h => hij (Fin.ext h)
      rw [Matrix.diagonal_apply_ne _ hij]
      simp [hn]
  unfold clearControlCode encode
  change (_, _, _) = (c.1, _, List.ofFn fun k : Fin c.2.2.length => _)
  rw [hA]
  congr 2
  apply List.ext_getElem
  · simp
  · intro k h₁ h₂
    have hk : k < c.2.2.length := by simpa using h₂
    simp only [List.getElem_map, List.getElem_ofFn]
    let l := c.2.2[k]
    have hlen : l.length = c.1 * c.1 := hc.2 l (List.get_mem c.2.2 ⟨k, hk⟩)
    have hB : matrixEntries (c.decode.control ⟨k, hk⟩) = l :=
      matrixEntries_getD_roundtrip c.1 l hlen
    have hclear : matrixEntries
        (c.decode.clearControlDenominators.control ⟨k, hk⟩) =
        clearDenominators (matrixEntries (c.decode.control ⟨k, hk⟩)) :=
      matrixEntries_getD_roundtrip c.1 _ ((clearDenominators_length _).trans
        (matrixEntries_length _))
    exact (hclear.trans (congrArg clearDenominators hB)).symm

theorem clearControlCode_correct (c : RationalPlantCode) (hc : c.WellFormed)
    (hdim : 2 ≤ c.1)
    (hdrift : c.decode.drift = Matrix.diagonal (fun i => if i.val = 0 then 1 else 0))
    (hcomm : ∀ i j, Commute (c.decode.control i) (c.decode.control j)) :
    CanonicalIntegerInstance (clearControlCode c) ∧
      (IntegerGlobalControllability (clearControlCode c) ↔ RationalGlobalControllability c) := by
  rw [clearControlCode_eq_encode c hc]
  let I := c.decode.clearControlDenominators
  refine ⟨⟨wellFormed_encode I, ?_⟩, ?_⟩
  · rw [decode_encode]
    exact c.decode.canonical_clearControlDenominators hdim hcomm
  · unfold IntegerGlobalControllability RationalGlobalControllability
    rw [decode_encode, and_iff_right (wellFormed_encode I), and_iff_right hc]
    exact c.decode.globallyControllable_clearControlDenominators hdrift

end PlantCode
end ContinuousBilinear
