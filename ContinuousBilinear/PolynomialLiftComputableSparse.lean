import ContinuousBilinear.PolynomialLiftComputableSupport
import Mathlib.Algebra.MvPolynomial.Rename

namespace ContinuousBilinear
namespace PolynomialLift

/-- A finite sum of monomials stored as coefficient/exponent pairs.
Every operation takes the ambient number of variables explicitly. -/
abbrev SparseCode := List (ℤ × List ℕ)

namespace SparseCode

def constant (n : ℕ) (c : ℤ) : SparseCode := [(c, (List.range n).map (fun _ => 0))]

def variableCode (n i : ℕ) : SparseCode :=
  [(1, (List.range n).map fun j => if j = i then 1 else 0)]

def addExponents (n : ℕ) (a b : List ℕ) : List ℕ :=
  (List.range n).map fun i => a.getD i 0 + b.getD i 0

def scale (c : ℤ) (a : SparseCode) : SparseCode :=
  a.map fun t => (c * t.1, t.2)

def mul (n : ℕ) (a b : SparseCode) : SparseCode :=
  a.flatMap fun x => b.map fun y => (x.1 * y.1, addExponents n x.2 y.2)

def pow (n : ℕ) (a : SparseCode) : ℕ → SparseCode
  | 0 => constant n 1
  | k + 1 => mul n (pow n a k) a

def product (n : ℕ) (xs : List SparseCode) : SparseCode :=
  xs.foldr (mul n) (constant n 1)

/-- Coefficients in the list are summed over exactly equal exponent lists. -/
def coefficient (a : SparseCode) (e : List ℕ) : ℤ :=
  (a.map fun t => if t.2 = e then t.1 else 0).sum

def WellSized (n : ℕ) (a : SparseCode) : Prop := ∀ t ∈ a, t.2.length = n

open MvPolynomial

noncomputable def denote (n : ℕ) (a : SparseCode) : MvPolynomial (Fin n) ℤ :=
  (a.map fun t => monomial (listExponentVector n t.2) t.1).sum

theorem denote_append (n : ℕ) (a b : SparseCode) :
    denote n (a ++ b) = denote n a + denote n b := by
  simp [denote]

theorem denote_flatten (n : ℕ) (xs : List SparseCode) :
    denote n xs.flatten = (xs.map (denote n)).sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [denote_append, ih]

theorem denote_constant (n : ℕ) (c : ℤ) : denote n (constant n c) = C c := by
  have he : listExponentVector n ((List.range n).map (fun _ => 0)) = 0 := by
    ext i
    simp [i.isLt]
  change monomial (listExponentVector n ((List.range n).map fun _ => 0)) c + 0 = C c
  rw [he, add_zero]
  rfl

private theorem getD_variableCode (n i : ℕ) (j : Fin n) :
    ((List.range n).map (fun k => if k = i then (1 : ℕ) else 0)).getD j.val 0 =
      if j.val = i then 1 else 0 := by
  simp [j.isLt]

theorem denote_variableCode (n : ℕ) (i : Fin n) :
    denote n (variableCode n i.val) = X i := by
  have he : listExponentVector n
      ((List.range n).map (fun k => if k = i.val then (1 : ℕ) else 0)) = Finsupp.single i 1 := by
    ext j
    rw [listExponentVector_apply, getD_variableCode]
    by_cases h : j = i
    · subst j
      simp
    · have hne : j.val ≠ i.val := fun h' => h (Fin.ext h')
      simp [h, hne, Finsupp.single_eq_of_ne]
  simp [denote, variableCode, he, X]

theorem listExponentVector_addExponents (n : ℕ) (a b : List ℕ) :
    listExponentVector n (addExponents n a b) =
      listExponentVector n a + listExponentVector n b := by
  ext i
  simp [addExponents, i.isLt]

theorem denote_scale (n : ℕ) (c : ℤ) (a : SparseCode) :
    denote n (scale c a) = C c * denote n a := by
  induction a with
  | nil => simp [denote, scale]
  | cons x xs ih =>
    change monomial (listExponentVector n x.2) (c * x.1) + denote n (scale c xs) =
      C c * (monomial (listExponentVector n x.2) x.1 + denote n xs)
    rw [mul_add, C_mul_monomial, ih]

private theorem denote_mul_monomial (n : ℕ) (x : ℤ × List ℕ) (b : SparseCode) :
    denote n (b.map fun y => (x.1 * y.1, addExponents n x.2 y.2)) =
      monomial (listExponentVector n x.2) x.1 * denote n b := by
  induction b with
  | nil => simp [denote]
  | cons y ys ih =>
    change monomial (listExponentVector n (addExponents n x.2 y.2)) (x.1 * y.1) +
        denote n (ys.map fun y => (x.1 * y.1, addExponents n x.2 y.2)) =
      monomial (listExponentVector n x.2) x.1 *
        (monomial (listExponentVector n y.2) y.1 + denote n ys)
    rw [mul_add, monomial_mul_monomial, listExponentVector_addExponents, ih]

theorem denote_mul (n : ℕ) (a b : SparseCode) :
    denote n (mul n a b) = denote n a * denote n b := by
  induction a with
  | nil => simp [mul, denote]
  | cons x xs ih =>
    change denote n ((b.map fun y => (x.1 * y.1, addExponents n x.2 y.2)) ++ mul n xs b) =
      (monomial (listExponentVector n x.2) x.1 + denote n xs) * denote n b
    rw [denote_append, add_mul, denote_mul_monomial, ih]

theorem denote_pow (n : ℕ) (a : SparseCode) (k : ℕ) :
    denote n (pow n a k) = denote n a ^ k := by
  induction k with
  | zero => simp [pow, denote_constant]
  | succ k ih => rw [pow, denote_mul, ih, pow_succ]

theorem denote_product (n : ℕ) (xs : List SparseCode) :
    denote n (product n xs) = (xs.map (denote n)).prod := by
  induction xs with
  | nil => simp [product, denote_constant]
  | cons a xs ih =>
    change denote n (mul n a (product n xs)) = denote n a * (xs.map (denote n)).prod
    rw [denote_mul, ih]

theorem wellSized_constant (n : ℕ) (c : ℤ) : WellSized n (constant n c) := by
  simp [WellSized, constant]

theorem wellSized_variable (n i : ℕ) : WellSized n (variableCode n i) := by
  simp [WellSized, variableCode]

theorem wellSized_mul (n : ℕ) (a b : SparseCode) : WellSized n (mul n a b) := by
  intro t ht
  obtain ⟨x, _, hx⟩ := List.mem_flatMap.mp ht
  obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
  simp [addExponents]

theorem wellSized_append (n : ℕ) (a b : SparseCode) (ha : WellSized n a)
    (hb : WellSized n b) : WellSized n (a ++ b) := by
  intro t ht
  rcases List.mem_append.mp ht with h | h
  · exact ha t h
  · exact hb t h

theorem wellSized_flatten (n : ℕ) (xs : List SparseCode)
    (h : ∀ a ∈ xs, WellSized n a) : WellSized n xs.flatten := by
  intro t ht
  obtain ⟨a, ha, ht⟩ := List.mem_flatten.mp ht
  exact h a ha t ht

theorem wellSized_scale (n : ℕ) (c : ℤ) (a : SparseCode) (ha : WellSized n a) :
    WellSized n (scale c a) := by
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  exact ha t ht

theorem wellSized_pow (n : ℕ) (a : SparseCode) (k : ℕ) : WellSized n (pow n a k) := by
  cases k
  · exact wellSized_constant _ _
  · exact wellSized_mul _ _ _

theorem wellSized_product (n : ℕ) (xs : List SparseCode) : WellSized n (product n xs) := by
  cases xs
  · exact wellSized_constant _ _
  · exact wellSized_mul _ _ _

theorem coefficient_eq_coeff (n : ℕ) (a : SparseCode) (ha : WellSized n a)
    (e : List ℕ) (he : e.length = n) :
    coefficient a e = (denote n a).coeff (listExponentVector n e) := by
  change _ = lcoeff ℤ (listExponentVector n e) _
  rw [denote, map_list_sum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  dsimp only [Function.comp_apply]
  rw [lcoeff_apply, coeff_monomial]
  by_cases h : t.2 = e
  · simp [h]
  · have hne : listExponentVector n t.2 ≠ listExponentVector n e := by
      intro h'
      apply h
      rw [← ofFn_listExponentVector t.2 (ha t ht), ← ofFn_listExponentVector e he, h']
    simp [h, hne]

theorem primrec_constant : Primrec₂ constant := by
  have hr : Primrec fun p : ℕ × ℤ => (List.range p.1).map (fun _ => (0 : ℕ)) :=
    Primrec.list_map (Primrec.list_range.comp Primrec.fst) (Primrec.const 0).to₂
  exact (Primrec.list_cons.comp (Primrec.snd.pair hr) (Primrec.const [])).to₂

theorem primrec_variableCode : Primrec₂ variableCode := by
  have hmap : Primrec fun p : ℕ × ℕ => (List.range p.1).map
      (fun j => if j = p.2 then (1 : ℕ) else 0) :=
    Primrec.list_map (Primrec.list_range.comp Primrec.fst)
      (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
        (Primrec.const 1) (Primrec.const 0)).to₂
  exact (Primrec.list_cons.comp ((Primrec.const (1 : ℤ)).pair hmap) (Primrec.const [])).to₂

theorem primrec_addExponents :
    Primrec (fun p : ℕ × List ℕ × List ℕ => addExponents p.1 p.2.1 p.2.2) := by
  exact Primrec.list_map (Primrec.list_range.comp Primrec.fst)
    (Primrec.nat_add.comp
      ((Primrec.list_getD 0).comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
      ((Primrec.list_getD 0).comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)).to₂

theorem primrec_scale : Primrec₂ scale := by
  apply Primrec₂.curry.mp
  exact Primrec.list_map Primrec.snd
    (((primrec_int_mul.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.snd.comp Primrec.snd))).to₂

theorem primrec_mul :
    Primrec (fun p : ℕ × SparseCode × SparseCode => mul p.1 p.2.1 p.2.2) := by
  have hinner : Primrec (fun a : (ℕ × SparseCode × SparseCode) × (ℤ × List ℕ) =>
      a.1.2.2.map fun y => (a.2.1 * y.1, addExponents a.1.1 a.2.2 y.2)) := by
    apply Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    let leftTerm : Primrec (fun a : (((ℕ × SparseCode × SparseCode) × (ℤ × List ℕ)) ×
        (ℤ × List ℕ)) => a.1.2) := Primrec.snd.comp Primrec.fst
    let rightTerm : Primrec (fun a : (((ℕ × SparseCode × SparseCode) × (ℤ × List ℕ)) ×
        (ℤ × List ℕ)) => a.2) := Primrec.snd
    have he := primrec_addExponents.comp
      ((Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
        ((Primrec.snd.comp leftTerm).pair (Primrec.snd.comp rightTerm)))
    exact ((primrec_int_mul.comp (Primrec.fst.comp leftTerm) (Primrec.fst.comp rightTerm)).pair he).to₂
  exact Primrec.list_flatMap (Primrec.fst.comp Primrec.snd) hinner.to₂

theorem primrec_pow : Primrec (fun p : ℕ × SparseCode × ℕ => pow p.1 p.2.1 p.2.2) := by
  have hstep : Primrec₂ (fun (p : ℕ × SparseCode × ℕ) (s : ℕ × SparseCode) =>
      mul p.1 s.2 p.2.1) :=
    (primrec_mul.comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.snd.comp Primrec.snd).pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))))).to₂
  refine (Primrec.nat_rec' (Primrec.snd.comp Primrec.snd)
    (primrec_constant.comp Primrec.fst (Primrec.const 1)) hstep).of_eq ?_
  rintro ⟨n, a, k⟩
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (fun xs => mul n xs a) ih

theorem primrec_product : Primrec₂ product := by
  apply Primrec₂.curry.mp
  exact Primrec.list_foldr Primrec.snd (primrec_constant.comp Primrec.fst (Primrec.const 1))
    (primrec_mul.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂

theorem primrec_coefficient : Primrec₂ coefficient := by
  apply Primrec₂.curry.mp
  have hterms : Primrec fun p : SparseCode × List ℕ => p.1.map
      (fun t => if t.2 = p.2 then t.1 else 0) :=
    Primrec.list_map Primrec.fst
      (Primrec.ite (Primrec.eq.comp (Primrec.snd.comp Primrec.snd)
          (Primrec.snd.comp Primrec.fst))
        (Primrec.fst.comp Primrec.snd) (Primrec.const 0)).to₂
  exact (Primrec.list_foldr hterms (Primrec.const 0)
    (primrec_int_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
      (fun p => by simp [coefficient, List.sum_eq_foldr])

end SparseCode
end PolynomialLift
end ContinuousBilinear
