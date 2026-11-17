import ContinuousBilinear.CompilerMatrixOperationsProof
import ContinuousBilinear.CompilerPlantTabulationProof

namespace ContinuousBilinear.GaussianPivot

/-- Size, row-major inverse, added column, added row, and corner of a bordered matrix. -/
abbrev Data := ℕ × List ℚ × List ℚ × List ℚ × ℚ

def entry (n : ℕ) (xs : List ℚ) (i j : ℕ) : ℚ :=
  xs.getD (i * n + j) 0

def matrixOfEntries (n : ℕ) (xs : List ℚ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of fun i j => entry n xs i.val j.val

/-- Finite scalar product, read from natural-indexed entry functions. -/
def sumProducts (n : ℕ) (f g : ℕ → ℚ) : ℚ :=
  ((List.range n).map fun i => f i * g i).sum

theorem sumProducts_eq_sum (n : ℕ) (f g : ℕ → ℚ) :
    sumProducts n f g = ∑ i : Fin n, f i.val * g i.val := by
  rw [sumProducts, ← List.sum_toFinset _ List.nodup_range, List.toFinset_range,
    ← Fin.sum_univ_eq_sum_range]

def inverseColumn (p : Data) (i : ℕ) : ℚ :=
  sumProducts p.1 (entry p.1 p.2.1 i) (fun j => p.2.2.1.getD j 0)

def rowInverse (p : Data) (j : ℕ) : ℚ :=
  sumProducts p.1 (fun i => p.2.2.2.1.getD i 0) (fun i => entry p.1 p.2.1 i j)

/-- Diagonal entry remaining after eliminating the selected row and column vectors. -/
def schurComplement (p : Data) : ℚ :=
  p.2.2.2.2 - sumProducts p.1 (fun i => p.2.2.2.1.getD i 0) (inverseColumn p)

def borderedEntry (p : Data) (i j : ℕ) : ℚ :=
  let r := (schurComplement p)⁻¹
  if i < p.1 then
    if j < p.1 then entry p.1 p.2.1 i j + (inverseColumn p i * r) * rowInverse p j
    else -(inverseColumn p i * r)
  else
    if j < p.1 then -(r * rowInverse p j) else r

/-- Update the inverse after a nonzero pivot. The added row and column are last. -/
@[irreducible] def borderedInverse (p : Data) : List ℚ :=
  PlantCode.tabulateMatrix (p.1 + 1) (borderedEntry p)

theorem computable_getD {α β : Type*} [Primcodable α] [Primcodable β]
    {xs : α → List β} {i : α → ℕ} (hxs : Computable xs) (hi : Computable i) (fallback : β) :
    Computable fun a => (xs a).getD (i a) fallback :=
  (Primrec.option_getD.to_comp.comp (Computable.list_getElem?.comp hxs hi)
    (Computable.const fallback)).of_eq fun _ => rfl

theorem computable_entry {α : Type*} [Primcodable α]
    {n : α → ℕ} {xs : α → List ℚ} {i j : α → ℕ}
    (hn : Computable n) (hx : Computable xs) (hi : Computable i) (hj : Computable j) :
    Computable fun a => entry (n a) (xs a) (i a) (j a) :=
  computable_getD hx (Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp hi hn) hj) 0

theorem computable_sumProducts {α : Type*} [Primcodable α] {n : α → ℕ}
    {f g : α → ℕ → ℚ} (hn : Computable n) (hf : Computable₂ f) (hg : Computable₂ g) :
    Computable fun a => sumProducts (n a) (f a) (g a) :=
  computable_rational_sum_range hn
    (computable_rat_mul.comp (show Computable _ from hf) (show Computable _ from hg)).to₂

private theorem computable_inverseColumn : Computable₂ inverseColumn := by
  change Computable (fun p : Data × ℕ => inverseColumn p.1 p.2)
  let hp : Computable (fun p : (Data × ℕ) × ℕ => p.1.1) :=
    Computable.fst.comp Computable.fst
  exact computable_sumProducts (Computable.fst.comp Computable.fst)
    (computable_entry (Computable.fst.comp hp) (Computable.fst.comp (Computable.snd.comp hp))
      (Computable.snd.comp Computable.fst) Computable.snd).to₂
    (computable_getD (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hp)))
      Computable.snd 0).to₂

private theorem computable_rowInverse : Computable₂ rowInverse := by
  change Computable (fun p : Data × ℕ => rowInverse p.1 p.2)
  let hp : Computable (fun p : (Data × ℕ) × ℕ => p.1.1) :=
    Computable.fst.comp Computable.fst
  exact computable_sumProducts (Computable.fst.comp Computable.fst)
    (computable_getD
      (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hp))))
      Computable.snd 0).to₂
    (computable_entry (Computable.fst.comp hp) (Computable.fst.comp (Computable.snd.comp hp))
      Computable.snd (Computable.snd.comp Computable.fst)).to₂

theorem computable_schurComplement : Computable schurComplement := by
  have hrow : Computable (fun p : Data × ℕ => p.1.2.2.2.1.getD p.2 0) :=
    computable_getD (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp Computable.fst)))) Computable.snd 0
  have hsum := computable_sumProducts Computable.fst hrow.to₂ computable_inverseColumn
  exact computable_rat_sub.comp (Computable.snd.comp (Computable.snd.comp
    (Computable.snd.comp Computable.snd))) hsum

private theorem computable_borderedEntry :
    Computable fun p : Data × ℕ × ℕ => borderedEntry p.1 p.2.1 p.2.2 := by
  let P := Data × ℕ × ℕ
  have hp : Computable (fun p : P => p.1) := Computable.fst
  have hi : Computable (fun p : P => p.2.1) := Computable.fst.comp Computable.snd
  have hj : Computable (fun p : P => p.2.2) := Computable.snd.comp Computable.snd
  have hn : Computable (fun p : P => p.1.1) := Computable.fst.comp hp
  have hrow := computable_rowInverse.comp hp hj
  have hcol := computable_inverseColumn.comp hp hi
  have hrec := computable_rat_inv.comp (computable_schurComplement.comp hp)
  have hij : Computable (fun p : P => entry p.1.1 p.1.2.1 p.2.1 p.2.2) :=
    computable_entry hn (Computable.fst.comp (Computable.snd.comp hp)) hi hj
  have hsmallI := (Primrec.nat_lt.decide.to_comp.comp hi hn).computablePred
  have hsmallJ := (Primrec.nat_lt.decide.to_comp.comp hj hn).computablePred
  have hc := computable_rat_mul.comp hcol hrec
  have hce := computable_rat_mul.comp hc hrow
  have hcr := computable_rat_mul.comp hrec hrow
  have hLeft := computable_cond_of_computablePred hsmallJ
    (computable_rat_add.comp hij hce) (computable_rat_neg.comp hc)
  have hRight := computable_cond_of_computablePred hsmallJ
    (computable_rat_neg.comp hcr) hrec
  have h := computable_cond_of_computablePred hsmallI hLeft hRight
  exact h.of_eq (g := fun p : P => borderedEntry p.1 p.2.1 p.2.2) fun _ => rfl

theorem computable_borderedInverse : Computable borderedInverse := by
  have hn : Computable (fun p : Data => p.1 + 1) :=
    Primrec.succ.to_comp.comp Computable.fst
  have h := PlantCode.computable_tabulateMatrix
    (n := fun p : Data => p.1 + 1) (f := fun p : Data × ℕ × ℕ => borderedEntry p.1 p.2.1 p.2.2)
    hn computable_borderedEntry
  exact h.of_eq (g := borderedInverse) fun p => by unfold borderedInverse; rfl

end ContinuousBilinear.GaussianPivot
