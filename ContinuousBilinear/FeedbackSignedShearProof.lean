import ContinuousBilinear.FeedbackShearLimitProof

namespace ContinuousBilinear.FeedbackData

open scoped Matrix
variable {d m : ℕ}

private abbrev axis (d : ℕ) : State (d + 1) := Fin.cases 1 0

private theorem scalarBlock_vecMul (v : State (d + 1)) (M : RealMatrix d) :
    v ᵥ* scalarBlock d (1, M) =
      Fin.cases (v 0) (Matrix.vecMul (fun i => v i.succ) M) := by
  funext j
  refine Fin.cases ?_ (fun a => ?_) j
  all_goals simp [Matrix.vecMul, dotProduct, scalarBlock, RingHom.coe_mk, Fin.sum_univ_succ]

private theorem shearToState_smul (r : ℝ) (x : State d) :
    shearToState (r • x) = r • shearToState x := by
  have h : liftState (r • x) = r • liftState x := by
    funext i; refine Fin.cases ?_ (fun a => ?_) i <;> simp
  simp [shearToState, h, Matrix.smul_vecMulVec]

private theorem shearToScalar_smul (r : ℝ) (x : State d) :
    shearToScalar (r • x) = r • shearToScalar x := by
  have h : liftState (r • x) = r • liftState x := by
    funext i; refine Fin.cases ?_ (fun a => ?_) i <;> simp
  simp [shearToScalar, h, Matrix.vecMulVec_smul]

private theorem shearToState_add (x y : State d) :
    shearToState (x + y) = shearToState x + shearToState y := by
  have h : liftState (x + y) = liftState x + liftState y := by
    funext i; refine Fin.cases ?_ (fun a => ?_) i <;> simp
  simp [shearToState, h, Matrix.add_vecMulVec]

private theorem shearToScalar_add (x y : State d) :
    shearToScalar (x + y) = shearToScalar x + shearToScalar y := by
  have h : liftState (x + y) = liftState x + liftState y := by
    funext i; refine Fin.cases ?_ (fun a => ?_) i <;> simp
  simp [shearToScalar, h, Matrix.vecMulVec_add]

private theorem liftState_zero : liftState (0 : State d) = 0 := by
  funext i
  refine Fin.cases ?_ (fun _ => ?_) i <;> rfl

private theorem shearToState_mul (x y : State d) :
    shearToState x * shearToState y = 0 := by
  simp [shearToState, Matrix.vecMulVec_mul_vecMulVec, dotProduct, Fin.sum_univ_succ]

private theorem shearToScalar_mul (x y : State d) :
    shearToScalar x * shearToScalar y = 0 := by
  simp [shearToScalar, Matrix.vecMulVec_mul_vecMulVec, dotProduct, Fin.sum_univ_succ]

private theorem conjugate_shearToState (M N : RealMatrix d) (hMN : M * N = 1) (w : State d) :
    scalarBlock d (1, M) * (1 + shearToState w) * scalarBlock d (1, N) =
      1 + shearToState (M.mulVec w) := by
  have hp : ((1, M) : ℝ × RealMatrix d) * (1, N) = 1 :=
    Prod.ext (mul_one 1) hMN
  rw [mul_add, mul_one, add_mul, ← map_mul, hp, map_one]
  simp only [
    shearToState, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, scalarBlock_mulVec, scalarBlock_vecMul,
    Fin.cases_zero, Fin.cases_succ, mul_zero, Matrix.zero_vecMul]

private theorem conjugate_shearToScalar (M N : RealMatrix d) (hMN : M * N = 1) (eta : State d) :
    scalarBlock d (1, M) * (1 + shearToScalar eta) * scalarBlock d (1, N) =
      1 + shearToScalar (Matrix.vecMul eta N) := by
  have hp : ((1, M) : ℝ × RealMatrix d) * (1, N) = 1 :=
    Prod.ext (mul_one 1) hMN
  rw [mul_add, mul_one, add_mul, ← map_mul, hp, map_one]
  simp only [
    shearToScalar, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, scalarBlock_mulVec, scalarBlock_vecMul,
    Fin.cases_zero, Fin.cases_succ, mul_one, Matrix.mulVec_zero]

private theorem orbitMatrix_mul_neg (F : FeedbackData d m)
    (hK : ∀ i j, Commute (F.K i) (F.K j)) (t : Fin m → ℝ) :
    F.orbitMatrix t * F.orbitMatrix (-t) = 1 := by
  rw [← F.orbitMatrix_add hK, add_neg_cancel, F.orbitMatrix_zero]

private theorem orbit_conjugation_state (F : FeedbackData d m)
    (hK : ∀ i j, Commute (F.K i) (F.K j)) (t : Fin m → ℝ) (w : State d)
    (hw : 1 + shearToState w ∈ (transitionMonoid F.plant).topologicalClosure) :
    1 + shearToState ((F.orbitMatrix t).mulVec w) ∈
      (transitionMonoid F.plant).topologicalClosure := by
  rw [← conjugate_shearToState _ _ (orbitMatrix_mul_neg F hK t)]
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _
    (F.scalarBlock_orbitMatrix_mem_topologicalClosure t) hw)
    (F.scalarBlock_orbitMatrix_mem_topologicalClosure (-t))

private theorem orbit_conjugation_scalar (F : FeedbackData d m)
    (hK : ∀ i j, Commute (F.K i) (F.K j)) (t : Fin m → ℝ) (eta : State d)
    (hw : 1 + shearToScalar eta ∈ (transitionMonoid F.plant).topologicalClosure) :
    1 + shearToScalar (Matrix.vecMul eta (F.orbitMatrix t)) ∈
      (transitionMonoid F.plant).topologicalClosure := by
  have h := orbitMatrix_mul_neg F hK (-t)
  rw [neg_neg] at h
  rw [← conjugate_shearToScalar _ _ h]
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _
    (F.scalarBlock_orbitMatrix_mem_topologicalClosure (-t)) hw)
    (F.scalarBlock_orbitMatrix_mem_topologicalClosure t)

private theorem scale_conjugation_state (F : FeedbackData d m) {a : ℝ} (ha : 0 < a) (w : State d)
    (hw : 1 + shearToState w ∈ (transitionMonoid F.plant).topologicalClosure) :
    1 + shearToState (a • w) ∈ (transitionMonoid F.plant).topologicalClosure := by
  have h : (a • (1 : RealMatrix d)) * (a⁻¹ • (1 : RealMatrix d)) = 1 := by
    simp [smul_smul, ha.ne']
  have hp : ((a • (1 : RealMatrix d))).mulVec w = a • w := by
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [← hp, ← conjugate_shearToState _ _ h]
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _
    (F.scalarBlock_pos_smul_mem_topologicalClosure ha) hw)
    (F.scalarBlock_pos_smul_mem_topologicalClosure (inv_pos.mpr ha))

private theorem scale_conjugation_scalar (F : FeedbackData d m) {a : ℝ} (ha : 0 < a) (eta : State d)
    (hw : 1 + shearToScalar eta ∈ (transitionMonoid F.plant).topologicalClosure) :
    1 + shearToScalar (a • eta) ∈ (transitionMonoid F.plant).topologicalClosure := by
  have h : (a⁻¹ • (1 : RealMatrix d)) * (a • (1 : RealMatrix d)) = 1 := by
    simp [smul_smul, ha.ne']
  have hp : Matrix.vecMul eta (a • (1 : RealMatrix d)) = a • eta := by
    rw [Matrix.vecMul_smul, Matrix.vecMul_one]
  rw [← hp, ← conjugate_shearToScalar _ _ h]
  exact Submonoid.mul_mem _ (Submonoid.mul_mem _
    (F.scalarBlock_pos_smul_mem_topologicalClosure (inv_pos.mpr ha)) hw)
    (F.scalarBlock_pos_smul_mem_topologicalClosure ha)

private theorem negative_base_shears_mem_topologicalClosure (F : FeedbackData d m)
    (hK : ∀ i j, Commute (F.K i) (F.K j)) (hneg : F.HasNegativePairing) :
    1 + shearToState (-F.b) ∈ (transitionMonoid F.plant).topologicalClosure ∧
    1 + shearToScalar (-F.ell) ∈ (transitionMonoid F.plant).topologicalClosure := by
  obtain ⟨t, ht⟩ := hneg
  let w := (F.orbitMatrix t).mulVec F.b
  let gamma := F.pairing w
  let beta := -(gamma⁻¹)
  let S : Submonoid (RealMatrix (d + 1)) := (transitionMonoid F.plant).topologicalClosure
  have hg : gamma < 0 := ht
  have hb : 0 < beta := neg_pos.mpr (inv_lt_zero.mpr hg)
  have hd : dotProduct (beta • F.ell) w = (-1 : ℝ) := by
    rw [smul_dotProduct]
    change -(gamma⁻¹) * gamma = -1
    rw [neg_mul, inv_mul_cancel₀ hg.ne]
  have hU : 1 + shearToState w ∈ S :=
    orbit_conjugation_state F hK t F.b (by
      simpa using F.nonnegativeShearToState_mem_topologicalClosure (t := 1) zero_le_one)
  have hL : 1 + shearToScalar (beta • F.ell) ∈ S := by
    rw [shearToScalar_smul]
    exact F.nonnegativeShearToScalar_mem_topologicalClosure hb.le
  have h := submonoid_mem_inverse_shears S hU hL
    (shearToState_sq w) (shearToScalar_sq (beta • F.ell))
    (by rw [shearToState_mul_shearToScalar_mul_shearToState, hd, neg_one_smul])
    (by rw [shearToScalar_mul_shearToState_mul_shearToScalar, hd, neg_one_smul])
  have hUn : 1 + shearToState (-w) ∈ S := by
    have hUneg : shearToState (-w) = -shearToState w := by
      rw [← neg_one_smul ℝ w, shearToState_smul, neg_one_smul]
    simpa [hUneg, sub_eq_add_neg] using h.1
  have hLn : 1 + shearToScalar (-(beta • F.ell)) ∈ S := by
    have hLneg (eta : State d) : shearToScalar (-eta) = -shearToScalar eta := by
      rw [← neg_one_smul ℝ eta, shearToScalar_smul, neg_one_smul]
    simpa [hLneg, sub_eq_add_neg] using h.2
  constructor
  · have hu := orbit_conjugation_state F hK (-t) (-w) hUn
    dsimp only [w] at hu
    have hinv := orbitMatrix_mul_neg F hK (-t)
    rw [neg_neg] at hinv
    rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] at hu
    exact hu
  · have hl := scale_conjugation_scalar F (a := beta⁻¹) (inv_pos.mpr hb)
      (-(beta • F.ell)) hLn
    simpa [smul_neg, smul_smul, inv_mul_cancel₀ hb.ne'] using hl

/-- Every signed shear belongs to the transition closure once one orbit pairing
is negative and both the column and row orbits span. -/
theorem shears_mem_topologicalClosure (F : FeedbackData d m)
    (hF : F.Hypotheses) (hneg : F.HasNegativePairing) :
    (∀ w : State d, 1 + shearToState w ∈ (transitionMonoid F.plant).topologicalClosure) ∧
    (∀ eta : State d, 1 + shearToScalar eta ∈ (transitionMonoid F.plant).topologicalClosure) := by
  obtain ⟨hK, _, hColumn, hRow⟩ := hF
  obtain ⟨hU, hL⟩ := negative_base_shears_mem_topologicalClosure F hK hneg
  let S : Submonoid (RealMatrix (d + 1)) := (transitionMonoid F.plant).topologicalClosure
  have hUb (c : ℝ) : 1 + shearToState (c • F.b) ∈ S := by
    by_cases h : 0 ≤ c
    · rw [shearToState_smul]
      exact F.nonnegativeShearToState_mem_topologicalClosure h
    · have h' : 1 + shearToState ((-c) • (-F.b)) ∈ S :=
        scale_conjugation_state F (by linarith) (-F.b) hU
      simpa [smul_neg] using h'
  have hLl (c : ℝ) : 1 + shearToScalar (c • F.ell) ∈ S := by
    by_cases h : 0 ≤ c
    · rw [shearToScalar_smul]
      exact F.nonnegativeShearToScalar_mem_topologicalClosure h
    · have h' : 1 + shearToScalar ((-c) • (-F.ell)) ∈ S :=
        scale_conjugation_scalar F (by linarith) (-F.ell) hL
      simpa [smul_neg] using h'
  constructor
  · intro w
    have hm : w ∈ Submodule.span ℝ (Set.range fun t => (F.orbitMatrix t).mulVec F.b) := by
      rw [hColumn]; exact Submodule.mem_top
    suffices h : ∀ c : ℝ, 1 + shearToState (c • w) ∈ S by
      change 1 + shearToState w ∈ S
      simpa using h 1
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      intro c
      have h' : 1 + shearToState ((F.orbitMatrix t).mulVec (c • F.b)) ∈ S :=
        orbit_conjugation_state F hK t (c • F.b) (hUb c)
      simpa [Matrix.mulVec_smul] using h'
    | zero =>
      intro c
      simpa only [smul_zero, shearToState, liftState_zero, Matrix.zero_vecMulVec, add_zero]
        using S.one_mem
    | add x y _ _ hx hy =>
      intro c
      rw [smul_add, shearToState_add]
      have h : (1 + shearToState (c • x)) * (1 + shearToState (c • y)) =
          1 + (shearToState (c • x) + shearToState (c • y)) := by
        simp [add_mul, mul_add, shearToState_mul, add_assoc]
      rw [← h]
      exact S.mul_mem (hx c) (hy c)
    | smul a x _ hx =>
      intro c
      rw [smul_smul]
      exact hx (c * a)
  · intro eta
    have hm : eta ∈ Submodule.span ℝ (Set.range fun t => Matrix.vecMul F.ell (F.orbitMatrix t)) := by
      change eta ∈ Submodule.span ℝ (Set.range fun t =>
        fun j => ∑ i, F.ell i * F.orbitMatrix t i j)
      rw [hRow]; exact Submodule.mem_top
    suffices h : ∀ c : ℝ, 1 + shearToScalar (c • eta) ∈ S by
      change 1 + shearToScalar eta ∈ S
      simpa using h 1
    induction hm using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      intro c
      have h' : 1 + shearToScalar (Matrix.vecMul (c • F.ell) (F.orbitMatrix t)) ∈ S :=
        orbit_conjugation_scalar F hK t (c • F.ell) (hLl c)
      simpa [Matrix.smul_vecMul] using h'
    | zero =>
      intro c
      simpa only [smul_zero, shearToScalar, liftState_zero, Matrix.vecMulVec_zero, add_zero]
        using S.one_mem
    | add x y _ _ hx hy =>
      intro c
      rw [smul_add, shearToScalar_add]
      have h : (1 + shearToScalar (c • x)) * (1 + shearToScalar (c • y)) =
          1 + (shearToScalar (c • x) + shearToScalar (c • y)) := by
        simp [add_mul, mul_add, shearToScalar_mul, add_assoc]
      rw [← h]
      exact S.mul_mem (hx c) (hy c)
    | smul a x _ hx =>
      intro c
      rw [smul_smul]
      exact hx (c * a)

end ContinuousBilinear.FeedbackData
