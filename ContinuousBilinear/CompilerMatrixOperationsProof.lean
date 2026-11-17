import ContinuousBilinear.CompilerRationalArithmeticProof
import Mathlib.Order.Interval.Finset.Nat

namespace ContinuousBilinear

/-- Sum a computable rational sequence over a computable finite range. -/
theorem computable_rational_sum_range {α : Type*} [Primcodable α]
    {n : α → ℕ} {f : α → ℕ → ℚ} (hn : Computable n) (hf : Computable₂ f) :
    Computable fun a => ((List.range (n a)).map (f a)).sum := by
  have hstep : Computable₂ (fun (p : α × ℕ) (s : ℕ × ℚ) => s.2 + f p.1 s.1) :=
    (computable_rat_add.comp (Computable.snd.comp Computable.snd)
      (hf.comp (Computable.fst.comp Computable.fst) (Computable.fst.comp Computable.snd))).to₂
  have hsum : Computable₂ (fun a (j : ℕ) => ((List.range j).map (f a)).sum) := by
    change Computable fun p : α × ℕ => ((List.range p.2).map (f p.1)).sum
    refine (Computable.nat_rec Computable.snd (Computable.const (0 : ℚ)) hstep).of_eq ?_
    intro p
    rcases p with ⟨a, j⟩
    induction j with
    | zero => rfl
    | succ j ih => simp [List.range_succ, ih]
  exact hsum.comp Computable.id hn

namespace PlantCode

/-- Matrix multiplication computed from natural-indexed entry functions. -/
def productEntries (n : ℕ) (a b : ℕ → ℕ → ℚ) (i j : ℕ) : ℚ :=
  ((List.range n).map fun k => a i k * b k j).sum

theorem computable_productEntries {α : Type*} [Primcodable α]
    {n : α → ℕ} {a b : α × ℕ × ℕ → ℚ}
    (hn : Computable n) (ha : Computable a) (hb : Computable b) :
    Computable fun p : α × ℕ × ℕ =>
      productEntries (n p.1) (fun i j => a (p.1, i, j)) (fun i j => b (p.1, i, j)) p.2.1 p.2.2 := by
  apply computable_rational_sum_range (hn.comp Computable.fst)
  have hparam : Computable fun p : (α × ℕ × ℕ) × ℕ => p.1.1 :=
    Computable.fst.comp Computable.fst
  have hrow : Computable fun p : (α × ℕ × ℕ) × ℕ => p.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hcol : Computable fun p : (α × ℕ × ℕ) × ℕ => p.1.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  exact (computable_rat_mul.comp
    (ha.comp (hparam.pair (hrow.pair Computable.snd)))
    (hb.comp (hparam.pair (Computable.snd.pair hcol)))).to₂

theorem productEntries_eq_matrix_mul {n : ℕ} {a b : ℕ → ℕ → ℚ}
    {A B : Matrix (Fin n) (Fin n) ℚ}
    (ha : ∀ i j : Fin n, a i.val j.val = A i j)
    (hb : ∀ i j : Fin n, b i.val j.val = B i j) (i j : Fin n) :
    productEntries n a b i.val j.val = (A * B) i j := by
  unfold productEntries
  rw [← List.sum_toFinset _ (List.nodup_range), List.toFinset_range,
    ← Fin.sum_univ_eq_sum_range]
  refine (Finset.sum_congr rfl (fun k _ => ?_)).trans Matrix.mul_apply.symm
  rw [ha, hb]

end PlantCode
end ContinuousBilinear
