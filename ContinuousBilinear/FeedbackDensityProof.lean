import ContinuousBilinear.FeedbackGenerationProof
import ContinuousBilinear.FeedbackSignedShearProof

namespace ContinuousBilinear.FeedbackData

open Matrix
variable {d m : ℕ}

private theorem shearToState_single (i : Fin d) (a : ℝ) :
    shearToState (Pi.single i a) = single i.succ 0 a := by
  ext k l
  refine Fin.cases ?_ (fun k => ?_) k <;> refine Fin.cases ?_ (fun l => ?_) l
  all_goals simp [shearToState, Matrix.vecMulVec, Matrix.single, Pi.single_apply, eq_comm]

private theorem shearToScalar_single (j : Fin d) (a : ℝ) :
    shearToScalar (Pi.single j a) = single 0 j.succ a := by
  ext k l
  refine Fin.cases ?_ (fun k => ?_) k <;> refine Fin.cases ?_ (fun l => ?_) l
  all_goals simp [shearToScalar, Matrix.vecMulVec, Matrix.single, Pi.single_apply, eq_comm]

private theorem transvection_succ_succ (i j : Fin d) (hij : i ≠ j) (a : ℝ) :
    transvection i.succ 0 a * transvection 0 j.succ (1 : ℝ) *
      transvection i.succ 0 (-a) * transvection 0 j.succ (-1 : ℝ) =
    transvection i.succ j.succ a := by
  have hi : (0 : Fin (d + 1)) ≠ i.succ := (Fin.succ_ne_zero i).symm
  simp [transvection, add_mul, mul_add, hi, hij.symm, ← Matrix.single_neg]
  abel

theorem transvections_mem_topologicalClosure (F : FeedbackData d m)
    (hF : F.Hypotheses) (hneg : F.HasNegativePairing)
    (i j : Fin (d + 1)) (hij : i ≠ j) (a : ℝ) :
    transvection i j a ∈ (transitionMonoid F.plant).topologicalClosure := by
  obtain ⟨hState, hScalar⟩ := F.shears_mem_topologicalClosure hF hneg
  let S := (transitionMonoid F.plant).topologicalClosure
  have hu (k : Fin d) (c : ℝ) : transvection k.succ 0 c ∈ S := by
    simpa [shearToState_single, transvection] using hState (Pi.single k c)
  have hl (k : Fin d) (c : ℝ) : transvection 0 k.succ c ∈ S := by
    simpa [shearToScalar_single, transvection] using hScalar (Pi.single k c)
  revert hij
  refine Fin.cases ?_ (fun x => ?_) i <;> refine Fin.cases ?_ (fun y => ?_) j
  · exact fun h => (h rfl).elim
  · exact fun _ => hl _ _
  · exact fun _ => hu _ _
  · intro h
    rw [← transvection_succ_succ x y (fun hxy => h (congrArg Fin.succ hxy)) a]
    exact S.mul_mem (S.mul_mem (S.mul_mem (hu x _) (hl y _)) (hu x _)) (hl y _)

/-- In the presence of a negative orbit pairing, the closure of the transitions
contains every real matrix with positive determinant. -/
theorem positive_det_mem_topologicalClosure (F : FeedbackData d m)
    (hF : F.Hypotheses) (hneg : F.HasNegativePairing)
    {A : RealMatrix (d + 1)} (hA : 0 < A.det) :
    A ∈ (transitionMonoid F.plant).topologicalClosure := by
  have hd : d ≠ 0 := by
    intro h
    subst d
    have hh := hF.2.1
    simp [pairing] at hh
  exact F.positive_det_mem_topologicalClosure_of_transvections hd
    (fun i j hij a => F.transvections_mem_topologicalClosure hF hneg i j hij a) hA

end ContinuousBilinear.FeedbackData
