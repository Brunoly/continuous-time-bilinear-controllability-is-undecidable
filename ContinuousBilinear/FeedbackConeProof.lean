import ContinuousBilinear.Feedback
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ContinuousBilinear.FeedbackData

open scoped Matrix Matrix.Norms.Operator
open NormedSpace

variable {d m : ℕ}

private def orbitGenerator (F : FeedbackData d m) (t : Fin m → ℝ) : RealMatrix d :=
  ∑ i, t i • F.K i

private theorem orbitGenerator_commute (F : FeedbackData d m)
    (hK : ∀ i j, Commute (F.K i) (F.K j)) (t u : Fin m → ℝ) :
    Commute (orbitGenerator F t) (orbitGenerator F u) := by
  apply Commute.sum_left
  intro i _
  apply Commute.sum_right
  intro j _
  exact ((hK i j).smul_left (t i)).smul_right (u j)

theorem orbitMatrix_add (F : FeedbackData d m)
    (hK : ∀ i j, Commute (F.K i) (F.K j)) (t u : Fin m → ℝ) :
    F.orbitMatrix (t + u) = F.orbitMatrix t * F.orbitMatrix u := by
  have hsum : orbitGenerator F (t + u) = orbitGenerator F t + orbitGenerator F u := by
    simp [orbitGenerator, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  change exp (orbitGenerator F (t + u)) = exp (orbitGenerator F t) * exp (orbitGenerator F u)
  rw [hsum, Matrix.exp_add_of_commute _ _ (orbitGenerator_commute F hK t u)]

@[simp] theorem orbitMatrix_zero (F : FeedbackData d m) : F.orbitMatrix 0 = 1 := by
  simp [FeedbackData.orbitMatrix]

/-- The cone consists of nonnegative scalar coordinates and states with nonnegative
pairing against every row of the exponential orbit. -/
def nonnegativeOrbitCone (F : FeedbackData d m) : Set (State (d + 1)) :=
  {x | 0 ≤ x 0 ∧ ∀ t : Fin m → ℝ,
    0 ≤ F.pairing ((F.orbitMatrix t).mulVec (fun i => x i.succ))}

private theorem pairing_add (F : FeedbackData d m) (x y : State d) :
    F.pairing (x + y) = F.pairing x + F.pairing y := by
  simp [pairing, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem pairing_smul (F : FeedbackData d m) (a : ℝ) (x : State d) :
    F.pairing (a • x) = a * F.pairing x := by
  simp only [pairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem isClosed_nonnegativeOrbitCone (F : FeedbackData d m) :
    IsClosed F.nonnegativeOrbitCone := by
  have eq_inter : F.nonnegativeOrbitCone =
      {x : State (d + 1) | 0 ≤ x 0} ∩
      ⋂ t : Fin m → ℝ, {x : State (d + 1) |
        0 ≤ F.pairing ((F.orbitMatrix t).mulVec (fun i => x i.succ))} := by
    ext x
    simp [nonnegativeOrbitCone]
  rw [eq_inter]
  apply IsClosed.inter (isClosed_le continuous_const (continuous_apply 0))
  apply isClosed_iInter
  intro t
  apply isClosed_le continuous_const
  unfold pairing Matrix.mulVec dotProduct
  fun_prop

theorem add_mem_nonnegativeOrbitCone (F : FeedbackData d m) {x y : State (d + 1)}
    (hx : x ∈ F.nonnegativeOrbitCone) (hy : y ∈ F.nonnegativeOrbitCone) :
    x + y ∈ F.nonnegativeOrbitCone := by
  refine ⟨add_nonneg hx.1 hy.1, fun t => ?_⟩
  change 0 ≤ F.pairing ((F.orbitMatrix t).mulVec
    ((fun i => x i.succ) + (fun i => y i.succ)))
  rw [Matrix.mulVec_add, pairing_add]
  exact add_nonneg (hx.2 t) (hy.2 t)

theorem smul_mem_nonnegativeOrbitCone (F : FeedbackData d m) {x : State (d + 1)}
    (hx : x ∈ F.nonnegativeOrbitCone) {a : ℝ} (ha : 0 ≤ a) :
    a • x ∈ F.nonnegativeOrbitCone := by
  refine ⟨mul_nonneg ha hx.1, fun t => ?_⟩
  change 0 ≤ F.pairing ((F.orbitMatrix t).mulVec (a • (fun i => x i.succ)))
  rw [Matrix.mulVec_smul, pairing_smul]
  exact mul_nonneg ha (hx.2 t)

theorem nonnegativeOrbitCone_pairing (F : FeedbackData d m) {x : State (d + 1)}
    (hx : x ∈ F.nonnegativeOrbitCone) :
    0 ≤ F.pairing (fun i => x i.succ) := by
  simpa using hx.2 0

private theorem finCases_mem_nonnegativeOrbitCone (F : FeedbackData d m) (a : ℝ) (z : State d)
    (ha : 0 ≤ a) (hz : ∀ t, 0 ≤ F.pairing ((F.orbitMatrix t).mulVec z)) :
    (Fin.cases a z) ∈ F.nonnegativeOrbitCone := by
  exact ⟨ha, hz⟩

theorem drift_mulVec (F : FeedbackData d m) (x : State (d + 1)) :
    F.plant.drift.mulVec x =
      ((x 0 + F.pairing (fun i => x i.succ)) / 2) • Fin.cases 1 F.b := by
  funext i
  change (∑ j : Fin (d + 1), ((1 / 2 : ℝ) * Fin.cases 1 F.b i * Fin.cases 1 F.ell j) * x j) =
    ((x 0 + F.pairing (fun j => x j.succ)) / 2) * Fin.cases 1 F.b i
  simp only [Fin.sum_univ_succ, Fin.cases_zero, Fin.cases_succ, mul_one, pairing]
  simp_rw [mul_assoc ((1 / 2 : ℝ) * Fin.cases 1 F.b i)]
  rw [← Finset.mul_sum]
  ring

theorem drift_preserves_nonnegativeOrbitCone (F : FeedbackData d m)
    (hn : ¬ F.HasNegativePairing) {x : State (d + 1)} (hx : x ∈ F.nonnegativeOrbitCone) :
    F.plant.drift.mulVec x ∈ F.nonnegativeOrbitCone := by
  rw [drift_mulVec]
  apply F.smul_mem_nonnegativeOrbitCone
  · exact F.finCases_mem_nonnegativeOrbitCone 1 F.b zero_le_one fun t =>
      le_of_not_gt fun ht => hn ⟨t, ht⟩
  · exact div_nonneg (add_nonneg hx.1 (F.nonnegativeOrbitCone_pairing hx)) (by norm_num)

/-- Block diagonal matrix acting by one scalar and one square matrix. -/
def scalarBlock (d : ℕ) : ℝ × RealMatrix d →+* RealMatrix (d + 1) where
  toFun p := Matrix.of fun i j => Fin.cases (Fin.cases p.1 0 j)
    (fun a => Fin.cases 0 (p.2 a) j) i
  map_zero' := by
    ext i j
    refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j <;> rfl
  map_add' := by
    intro p q
    ext i j
    refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j <;> simp
  map_one' := by
    ext i j
    refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
    all_goals simp [Matrix.one_apply, eq_comm]
  map_mul' := by
    intro p q
    ext i j
    refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
    all_goals simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem scalarBlock_mulVec (p : ℝ × RealMatrix d) (x : State (d + 1)) :
    (scalarBlock d p).mulVec x = Fin.cases (p.1 * x 0) (p.2.mulVec (fun i => x i.succ)) := by
  funext i
  refine Fin.cases ?_ (fun a => ?_) i
  all_goals simp [scalarBlock, RingHom.coe_mk, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private theorem continuous_scalarBlock (d : ℕ) : Continuous (scalarBlock d) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
  · exact continuous_fst
  · exact continuous_const
  · exact continuous_const
  · change Continuous (fun p : ℝ × RealMatrix d => p.2 a b)
    fun_prop

theorem exp_scalarBlock (r : ℝ) (M : RealMatrix d) :
    exp (scalarBlock d (r, M)) = scalarBlock d (exp r, exp M) := by
  calc
    _ = scalarBlock d (exp (r, M)) := (NormedSpace.map_exp
      (scalarBlock d) (continuous_scalarBlock d) (r, M)).symm
    _ = _ := congrArg (scalarBlock d) (Prod.ext (Prod.fst_exp _) (Prod.snd_exp _))

theorem scalarBlock_orbitMatrix_preserves_nonnegativeOrbitCone (F : FeedbackData d m)
    (hK : ∀ i j, Commute (F.K i) (F.K j)) {r : ℝ} (hr : 0 ≤ r)
    (u : Fin m → ℝ) {x : State (d + 1)} (hx : x ∈ F.nonnegativeOrbitCone) :
    (scalarBlock d (r, F.orbitMatrix u)).mulVec x ∈ F.nonnegativeOrbitCone := by
  rw [scalarBlock_mulVec]
  apply F.finCases_mem_nonnegativeOrbitCone _ _ (mul_nonneg hr hx.1)
  intro t
  rw [Matrix.mulVec_mulVec, ← F.orbitMatrix_add hK t u]
  exact hx.2 (t + u)

/-- The part of the generator that depends linearly on the control. -/
def controlGenerator (F : FeedbackData d m) (u : Fin (m + 1) → ℝ) :
    RealMatrix (d + 1) :=
  scalarBlock d (0, u 0 • 1 + orbitGenerator F (fun i => u i.succ))

theorem generator_eq_drift_add_controlGenerator (F : FeedbackData d m) (u : Fin (m + 1) → ℝ) :
    (generator F.plant u : RealMatrix (d + 1)) =
      @Add.add (RealMatrix (d + 1)) _ F.plant.drift (F.controlGenerator u) := by
  apply congrArg (fun M : RealMatrix (d + 1) => @Add.add _ _ F.plant.drift M)
  let C : Fin (m + 1) → RealMatrix (d + 1) := F.plant.control
  change (∑ k : Fin (m + 1), u k • C k) = F.controlGenerator u
  have h0 : C 0 = scalarBlock d (0, 1) := by
    change Matrix.diagonal (Fin.cases (0 : ℝ) (fun _ : Fin d => 1)) =
      scalarBlock d (0, 1)
    ext i j
    refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
    all_goals simp [scalarBlock, RingHom.coe_mk, Matrix.diagonal_apply, Matrix.one_apply, eq_comm]
  have hk (k : Fin m) : C k.succ = scalarBlock d (0, F.K k) := by
    let D : RealMatrix (d + 1) := Matrix.diagonal (Fin.cases 0 (fun _ : Fin d => 1))
    let K' (i : Fin m) : RealMatrix (d + 1) :=
      fun j k => Fin.cases 0 (fun a => Fin.cases 0 (F.K i a) k) j
    have hC : C = @Fin.cases m (fun _ => RealMatrix (d + 1)) D K' := rfl
    calc
      C k.succ = @Fin.cases m (fun _ => RealMatrix (d + 1)) D K' k.succ := congrFun hC k.succ
      _ = K' k := @Fin.cases_succ m (fun _ => RealMatrix (d + 1)) D K' k
      _ = _ := by
        ext i j
        refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
        all_goals rfl
  simp only [Fin.sum_univ_succ, h0, hk]
  ext i j
  refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
  all_goals simp [controlGenerator, orbitGenerator, scalarBlock, RingHom.coe_mk, Matrix.sum_apply]

theorem smul_controlGenerator (F : FeedbackData d m) (a : ℝ) (u : Fin (m + 1) → ℝ) :
    a • F.controlGenerator u = F.controlGenerator (a • u) := by
  have heq : a • (u 0 • (1 : RealMatrix d) + orbitGenerator F (fun i => u i.succ)) =
      (a * u 0) • (1 : RealMatrix d) + orbitGenerator F (fun i => a * u i.succ) := by
    simp [orbitGenerator, smul_add, Finset.smul_sum, smul_smul]
  ext i j
  refine Fin.cases ?_ (fun k => ?_) i <;> refine Fin.cases ?_ (fun l => ?_) j
  · simp [controlGenerator, scalarBlock, RingHom.coe_mk]
  · simp [controlGenerator, scalarBlock, RingHom.coe_mk]
  · simp [controlGenerator, scalarBlock, RingHom.coe_mk]
  · simpa [controlGenerator, scalarBlock, RingHom.coe_mk] using
      congrFun (congrFun heq k) l

/-- The flow of the control part separates into positive scaling and the exponential orbit. -/
theorem exp_controlGenerator (F : FeedbackData d m) (u : Fin (m + 1) → ℝ) :
    exp (F.controlGenerator u) = scalarBlock d (1, Real.exp (u 0) •
      F.orbitMatrix (fun i => u i.succ)) := by
  have hcomm : Commute (u 0 • (1 : RealMatrix d)) (orbitGenerator F (fun i => u i.succ)) :=
    (Commute.one_left _).smul_left _
  rw [controlGenerator, exp_scalarBlock, NormedSpace.exp_zero, Matrix.exp_add_of_commute _ _ hcomm]
  have he : exp (u 0 • (1 : RealMatrix d)) =
      algebraMap ℝ (RealMatrix d) (Real.exp (u 0)) := by
    rw [← Algebra.algebraMap_eq_smul_one, Real.exp_eq_exp_ℝ]
    exact (NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := RealMatrix d) (u 0)).symm
  rw [he, Algebra.smul_def]
  rfl

theorem exp_controlGenerator_preserves_nonnegativeOrbitCone (F : FeedbackData d m)
    (hK : ∀ i j, Commute (F.K i) (F.K j)) (u : Fin (m + 1) → ℝ)
    {x : State (d + 1)} (hx : x ∈ F.nonnegativeOrbitCone) :
    (exp (F.controlGenerator u)).mulVec x ∈ F.nonnegativeOrbitCone := by
  rw [F.exp_controlGenerator, scalarBlock_mulVec]
  apply F.finCases_mem_nonnegativeOrbitCone _ _ (by simpa using hx.1)
  intro t
  rw [Matrix.smul_mulVec, Matrix.mulVec_smul, pairing_smul, Matrix.mulVec_mulVec,
    ← F.orbitMatrix_add hK t (fun i => u i.succ)]
  exact mul_nonneg (Real.exp_pos _).le (hx.2 _)

end ContinuousBilinear.FeedbackData
