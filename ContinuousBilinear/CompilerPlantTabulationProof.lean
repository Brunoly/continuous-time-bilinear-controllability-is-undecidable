import ContinuousBilinear.CompilerDenominatorClearingProof

namespace ContinuousBilinear
namespace PlantCode

/-- Row-major tabulation using total natural-indexed entry functions. -/
def tabulateMatrix {R : Type*} (n : ℕ) (f : ℕ → ℕ → R) : List R :=
  (List.range (n * n)).map fun i => f (i / n) (i % n)

theorem tabulateMatrix_eq_matrixEntries {R : Type*} {n : ℕ}
    (f : ℕ → ℕ → R) (M : Matrix (Fin n) (Fin n) R)
    (h : ∀ i j : Fin n, f i.val j.val = M i j) :
    tabulateMatrix n f = matrixEntries M := by
  apply List.ext_getElem
  · simp [tabulateMatrix]
  · intro k h₁ h₂
    have hk : k < n * n := by simpa using h₂
    let u : Fin (n * n) := ⟨k, hk⟩
    simp only [tabulateMatrix, List.getElem_map, List.getElem_range, matrixEntries, List.getElem_ofFn]
    exact h (finProdFinEquiv.symm u).1 (finProdFinEquiv.symm u).2

theorem computable_tabulateMatrix {α R : Type*} [Primcodable α] [Primcodable R]
    {n : α → ℕ} {f : α × ℕ × ℕ → R} (hn : Computable n) (hf : Computable f) :
    Computable fun a => tabulateMatrix (n a) (fun i j => f (a, i, j)) := by
  unfold tabulateMatrix
  apply computable_list_map
    (Primrec.list_range.to_comp.comp (Primrec.nat_mul.to_comp.comp hn hn))
  exact (hf.comp (Computable.fst.pair
    ((Primrec.nat_div.to_comp.comp Computable.snd (hn.comp Computable.fst)).pair
      (Primrec.nat_mod.to_comp.comp Computable.snd (hn.comp Computable.fst))))).to₂

/-- Tabulate all drift and control entries from their finite matrix dimensions. -/
def tabulatePlant {R : Type*} (n m : ℕ) (drift : ℕ → ℕ → R)
    (control : ℕ → ℕ → ℕ → R) : PlantCode R :=
  (n, tabulateMatrix n drift, (List.range m).map fun k => tabulateMatrix n (control k))

theorem tabulatePlant_eq_encode {R : Type*} (P : Plant R) (drift : ℕ → ℕ → R)
    (control : ℕ → ℕ → ℕ → R)
    (hA : ∀ i j : Fin P.dimension, drift i.val j.val = P.drift i j)
    (hB : ∀ (k : Fin P.controls) (i j : Fin P.dimension),
      control k.val i.val j.val = P.control k i j) :
    tabulatePlant P.dimension P.controls drift control = encode P := by
  unfold tabulatePlant encode
  rw [tabulateMatrix_eq_matrixEntries _ _ hA]
  congr 2
  apply List.ext_getElem
  · simp
  · intro k h₁ h₂
    have hk : k < P.controls := by simpa using h₂
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
    exact tabulateMatrix_eq_matrixEntries _ _ (hB ⟨k, hk⟩)

theorem computable_tabulatePlant {α R : Type*} [Primcodable α] [Primcodable R]
    {n m : α → ℕ} {drift : α × ℕ × ℕ → R} {control : (α × ℕ) × ℕ × ℕ → R}
    (hn : Computable n) (hm : Computable m) (hA : Computable drift)
    (hB : Computable control) :
    Computable fun a => tabulatePlant (n a) (m a)
      (fun i j => drift (a, i, j)) (fun k i j => control ((a, k), i, j)) := by
  exact hn.pair ((computable_tabulateMatrix hn hA).pair
    (computable_list_map (Primrec.list_range.to_comp.comp hm)
      (computable_tabulateMatrix (hn.comp Computable.fst) hB).to₂))

end PlantCode
end ContinuousBilinear
