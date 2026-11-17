import ContinuousBilinear.Targets
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.OfFn

namespace ContinuousBilinear

namespace PlantCode

/-- List the entries of a square matrix with the column index varying fastest. -/
def matrixEntries {R : Type*} {n : ℕ} (M : Matrix (Fin n) (Fin n) R) : List R :=
  List.ofFn fun k : Fin (n * n) =>
    M (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2

/-- A row-major presentation of a plant. -/
def encode {R : Type*} (P : Plant R) : PlantCode R :=
  (P.dimension, matrixEntries P.drift, List.ofFn fun k => matrixEntries (P.control k))

@[simp] theorem matrixEntries_length {R : Type*} {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    (matrixEntries M).length = n * n := by
  simp [matrixEntries]

theorem matrixEntries_getD {R : Type*} {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (i j : Fin n) (d : R) :
    (matrixEntries M).getD (i.val * n + j.val) d = M i j := by
  have hval : (finProdFinEquiv (i, j)).val = i.val * n + j.val := by
    change j.val + n * i.val = _
    ac_rfl
  have hlt : i.val * n + j.val < n * n :=
    hval ▸ (finProdFinEquiv (i, j)).isLt
  have hget (f : Fin (n * n) → R) (d' : R) :
      (List.ofFn f).getD (i.val * n + j.val) d' = f ⟨_, hlt⟩ := by
    simp [List.getD_eq_getElem?_getD, hlt]
  have hindex : (⟨i.val * n + j.val, hlt⟩ : Fin (n * n)) = finProdFinEquiv (i, j) :=
    Fin.ext hval.symm
  calc
    _ = M (finProdFinEquiv.symm ⟨_, hlt⟩).1 (finProdFinEquiv.symm ⟨_, hlt⟩).2 :=
      hget (fun k => M (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) d
    _ = M i j := by rw [hindex, Equiv.symm_apply_apply]

theorem wellFormed_encode {R : Type*} (P : Plant R) : (encode P).WellFormed := by
  unfold WellFormed encode
  refine ⟨matrixEntries_length _, ?_⟩
  intro b hb
  rw [List.mem_ofFn] at hb
  obtain ⟨k, rfl⟩ := hb
  exact matrixEntries_length _

theorem decode_encode {R : Type*} [Zero R] (P : Plant R) : (encode P).decode = P := by
  rcases P with ⟨n, m, A, B⟩
  have hm : (List.ofFn fun k : Fin m => matrixEntries (B k)).length = m :=
    List.length_ofFn
  unfold encode decode
  simp only
  generalize hs : (List.ofFn fun k : Fin m => matrixEntries (B k)) = L at hm ⊢
  have hget (k : Fin L.length) : L.get k = matrixEntries (B (Fin.cast hm k)) := by
    subst L
    exact List.get_ofFn _ _
  cases hm
  simp only [hget, Fin.cast_refl, id_eq, matrixEntries_getD]

theorem wellFormed_map_iff {R S : Type*} (f : R → S) (c : PlantCode R) :
    (c.map f).WellFormed ↔ c.WellFormed := by
  simp [WellFormed, map]

theorem primrec_wellFormed {R : Type*} [Primcodable R] :
    PrimrecPred (WellFormed (R := R)) := by
  have hmul : Primrec (fun c : PlantCode R => c.1 * c.1) :=
    Primrec.nat_mul.comp Primrec.fst Primrec.fst
  have hA : PrimrecPred (fun c : PlantCode R => c.2.1.length = c.1 * c.1) :=
    Primrec.eq.comp (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)) hmul
  have hparams : Primrec (fun c : PlantCode R =>
      c.2.2.map (fun b => (c.1 * c.1, b))) :=
    Primrec.list_map (Primrec.snd.comp Primrec.snd)
      ((hmul.comp Primrec.fst).pair Primrec.snd).to₂
  have hlength : PrimrecPred fun p : ℕ × List R => p.2.length = p.1 :=
    Primrec.eq.comp (Primrec.list_length.comp Primrec.snd) Primrec.fst
  refine hA.and ?_
  exact ((PrimrecPred.forall_mem_list hlength).comp hparams).of_eq fun c => by simp

theorem computable_wellFormed {R : Type*} [Primcodable R] :
    ComputablePred (WellFormed (R := R)) := by
  obtain ⟨d, hd⟩ := primrec_wellFormed (R := R)
  exact ⟨d, hd.to_comp⟩

end PlantCode

theorem encodingCompleteness : Targets.EncodingCompleteness := by
  exact ⟨fun P => ⟨PlantCode.encode P, PlantCode.wellFormed_encode P, PlantCode.decode_encode P⟩,
    fun P => ⟨PlantCode.encode P, PlantCode.wellFormed_encode P, PlantCode.decode_encode P⟩⟩

private theorem plant_mk_eq_of_control_eq {R : Type*} {n m m' : ℕ}
    {A A' : Matrix (Fin n) (Fin n) R}
    {B : Fin m → Matrix (Fin n) (Fin n) R} {B' : Fin m' → Matrix (Fin n) (Fin n) R}
    (hm : m = m') (hA : A = A') (hB : ∀ k, B k = B' (Fin.cast hm k)) :
    Plant.mk n m A B = Plant.mk n m' A' B' := by
  subst m'
  subst A'
  have h : B = B' := funext hB
  subst B'
  rfl

theorem toReal_decode_map_intCast (c : IntegerPlantCode) :
    toReal (c.map (fun z : ℤ => (z : ℚ))).decode = toReal c.decode := by
  rcases c with ⟨n, A, B⟩
  have hcast (l : List ℤ) (i : ℕ) :
      (((l.map (fun z : ℤ => (z : ℚ))).getD i 0 : ℚ) : ℝ) = (l.getD i 0 : ℝ) := by
    have hmap : (l.map (fun z : ℤ => (z : ℚ))).getD i 0 = (l.getD i 0 : ℚ) := by
      simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
      cases l[i]? <;> simp
    rw [hmap, Rat.cast_intCast]
  apply plant_mk_eq_of_control_eq (List.length_map _)
  · ext i j
    exact hcast A _
  · intro k
    ext i j
    have hget : (B.map (List.map (fun z : ℤ => (z : ℚ)))).get k =
        (B.get (Fin.cast (List.length_map _) k)).map (fun z : ℤ => (z : ℚ)) := by
      simp [List.get_eq_getElem]
    -- Reduce the control list before reducing the entry cast.
    change ((((B.map (List.map (fun z : ℤ => (z : ℚ)))).get k).getD
      (i.val * n + j.val) 0 : ℚ) : ℝ) = _
    rw [hget]
    exact hcast _ _

theorem integerGlobalControllability_iff_rational (c : IntegerPlantCode) :
    IntegerGlobalControllability c ↔
      RationalGlobalControllability (c.map (fun z : ℤ => (z : ℚ))) := by
  rw [IntegerGlobalControllability, RationalGlobalControllability, toReal_decode_map_intCast, PlantCode.wellFormed_map_iff]

end ContinuousBilinear
