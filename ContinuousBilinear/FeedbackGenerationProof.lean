import ContinuousBilinear.FeedbackFastControlProof
import ContinuousBilinear.FeedbackGenerationAlgebraProof

namespace ContinuousBilinear

open Matrix

namespace FeedbackData
variable {d m : ℕ}
open scoped Matrix

theorem det_scalarBlock_smul_one (c : ℝ) :
    det (scalarBlock d (1, c • (1 : RealMatrix d))) = c ^ d := by
  have heq : scalarBlock d (1, c • (1 : RealMatrix d)) =
      Matrix.diagonal (Fin.cases 1 (fun _ : Fin d => c)) := by
    ext i j
    refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
    all_goals simp [scalarBlock, RingHom.coe_mk, Matrix.one_apply, Matrix.diagonal_apply, eq_comm]
  rw [heq, Matrix.det_diagonal, Fin.prod_univ_succ]
  simp

theorem positive_det_mem_topologicalClosure_of_transvections (F : FeedbackData d m)
    (hd : d ≠ 0) (hS : ∀ i j : Fin (d + 1), i ≠ j → ∀ a : ℝ,
      transvection i j a ∈ (transitionMonoid F.plant).topologicalClosure)
    {M : RealMatrix (d + 1)} (hM : 0 < det M) :
    M ∈ (transitionMonoid F.plant).topologicalClosure := by
  have : Nontrivial (Fin (d + 1)) := ⟨⟨0, ⟨1, by omega⟩, by
    intro h; have := congrArg Fin.val h; simp at this⟩⟩
  let c := Real.exp (Real.log (det M) / d)
  have hc : 0 < c := Real.exp_pos _
  have hpow : c ^ d = det M := by
    rw [show c = Real.exp (Real.log (det M) / d) from rfl, ← Real.exp_nat_mul]
    have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
    have he : (d : ℝ) * (Real.log (det M) / d) = Real.log (det M) := by
      field_simp [hd']
    rw [he, Real.exp_log hM]
  let D : RealMatrix (d + 1) := scalarBlock d (1, c • (1 : RealMatrix d))
  let Dinv : RealMatrix (d + 1) := scalarBlock d (1, c⁻¹ • (1 : RealMatrix d))
  have hinv : D * Dinv = 1 := by
    rw [show D = scalarBlock d (1, c • 1) from rfl,
      show Dinv = scalarBlock d (1, c⁻¹ • 1) from rfl, ← map_mul, ← (scalarBlock d).map_one]
    congr 1
    simp [smul_smul, hc.ne']
  have hdet : det (Dinv * M) = 1 := by
    rw [Matrix.det_mul, show det Dinv = c⁻¹ ^ d from det_scalarBlock_smul_one _, inv_pow,
      hpow, inv_mul_cancel₀ hM.ne']
  let S : Submonoid (RealMatrix (d + 1)) := (transitionMonoid F.plant).topologicalClosure
  have hnormal : Dinv * M ∈ S := det_one_mem_of_transvections S hS hdet
  have hscale : D ∈ S := F.scalarBlock_pos_smul_mem_topologicalClosure hc
  have hm := S.mul_mem hscale hnormal
  rw [← mul_assoc, hinv, one_mul] at hm
  exact hm

end FeedbackData
end ContinuousBilinear
