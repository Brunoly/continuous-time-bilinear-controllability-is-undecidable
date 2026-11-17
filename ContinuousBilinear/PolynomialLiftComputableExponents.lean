import ContinuousBilinear.PolynomialLift
import ContinuousBilinear.CompilerIntegerArithmeticProof

namespace ContinuousBilinear
namespace PolynomialLift

/-- All exponent lists with the given length and a coordinate bound. -/
def boxExponentLists (D : ℕ) : ℕ → List (List ℕ)
  | 0 => [[]]
  | n + 1 => (List.range (D + 1)).flatMap fun e => (boxExponentLists D n).map (e :: ·)

theorem mem_boxExponentLists (D n : ℕ) (a : List ℕ) :
    a ∈ boxExponentLists D n ↔ a.length = n ∧ ∀ e ∈ a, e ≤ D := by
  induction n generalizing a with
  | zero => cases a <;> simp [boxExponentLists]
  | succ n ih =>
    cases a with
    | nil => simp [boxExponentLists]
    | cons x a =>
      simp [boxExponentLists, ih, and_left_comm, and_comm]

theorem boxExponentLists_nodup (D n : ℕ) : (boxExponentLists D n).Nodup := by
  induction n with
  | zero => simp [boxExponentLists]
  | succ n ih =>
    unfold boxExponentLists
    apply List.nodup_flatMap.mpr
    constructor
    · intro e _
      exact ih.map (fun _ _ h => (List.cons.inj h).2)
    · rw [List.pairwise_iff_getElem]
      simp only [List.length_range, List.getElem_range]
      intro i j hi hj hij
      apply List.disjoint_left.mpr
      intro a ha hb
      obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
      obtain ⟨c, _, hc⟩ := List.mem_map.mp hb
      exact hij.ne (List.cons.inj hc).1.symm

theorem primrec_boxExponentLists : Primrec₂ boxExponentLists := by
  have hstep : Primrec₂ (fun (p : ℕ × ℕ) (s : ℕ × List (List ℕ)) =>
      (List.range (p.1 + 1)).flatMap fun e => s.2.map (e :: ·)) := by
    apply Primrec₂.curry.mp
    apply Primrec.list_flatMap (Primrec.list_range.comp
      (Primrec.succ.comp (Primrec.fst.comp Primrec.fst)))
    apply Primrec₂.curry.mp
    exact Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  apply Primrec₂.curry.mp
  refine (Primrec.nat_rec' Primrec.snd (Primrec.const ([[]] : List (List ℕ))) hstep).of_eq ?_
  rintro ⟨D, n⟩
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Function.curry] at ih
    simpa only [Function.curry, boxExponentLists] using congrArg
      (fun xs => (List.range (D + 1)).flatMap fun e => xs.map (e :: ·)) ih

theorem primrec_nat_listSum : Primrec (List.sum : List ℕ → ℕ) := by
  exact (Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
      (fun a => by simp [List.sum_eq_foldr])

/-- A duplicate-free enumeration of the degree-bounded exponent vectors. -/
def boundedExponentLists (D n : ℕ) : List (List ℕ) :=
  (boxExponentLists D n).filter fun a => a.sum ≤ D

theorem mem_boundedExponentLists (D n : ℕ) (a : List ℕ) :
    a ∈ boundedExponentLists D n ↔ a.length = n ∧ a.sum ≤ D := by
  rw [boundedExponentLists, List.mem_filter]
  simp only [mem_boxExponentLists, decide_eq_true_eq]
  refine ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, ?_⟩, h.2⟩⟩
  intro x hx
  exact (List.le_sum_of_mem hx).trans h.2

theorem boundedExponentLists_nodup (D n : ℕ) : (boundedExponentLists D n).Nodup :=
  (boxExponentLists_nodup D n).filter _

theorem primrec_boundedExponentLists : Primrec₂ boundedExponentLists := by
  have h : PrimrecRel (fun (a : List ℕ) (D : ℕ) => a.sum ≤ D) :=
    Primrec.nat_le.comp (primrec_nat_listSum.comp Primrec.fst) Primrec.snd
  exact h.listFilter.comp (Primrec₂.curry.mp primrec_boxExponentLists) Primrec.fst

theorem listGetD_of_lt {α : Type*} (l : List α) (d : α) {n : ℕ}
    (hn : n < l.length) : l.getD n d = l[n] := by
  simp only [List.getD_eq_getElem?_getD, getElem?_pos l n hn, Option.getD_some]

theorem listGetD_of_ge {α : Type*} (l : List α) (d : α) {n : ℕ}
    (hn : l.length ≤ n) : l.getD n d = d := by
  simp only [List.getD_eq_getElem?_getD, getElem?_neg l n (Nat.not_lt.mpr hn), Option.getD_none]

/-- Interpret a finite list of exponents by padding with zeros. -/
noncomputable def listExponentVector (n : ℕ) (a : List ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => a.getD i.val 0)

@[simp] theorem listExponentVector_apply (n : ℕ) (a : List ℕ) (i : Fin n) :
    listExponentVector n a i = a.getD i.val 0 := rfl

theorem ofFn_listExponentVector {n : ℕ} (a : List ℕ) (ha : a.length = n) :
    List.ofFn (listExponentVector n a) = a := by
  apply List.ext_getElem
  · simp [ha]
  · intro i hi hj
    simp [hj]

@[simp] theorem listExponentVector_ofFn {n : ℕ} (a : Fin n →₀ ℕ) :
    listExponentVector n (List.ofFn a) = a := by
  ext i
  simp [i.isLt]

theorem monomialDegree_listExponentVector {n : ℕ} (a : List ℕ) (ha : a.length = n) :
    monomialDegree (listExponentVector n a) = a.sum := by
  rw [← ofFn_listExponentVector a ha, List.sum_ofFn, monomialDegree]
  simp

theorem boundedExponentLists_exact (D n : ℕ) :
    {a | a ∈ boundedExponentLists D n} =
      Set.range (fun x : MonomialIndex (Fin n) D => List.ofFn x.val) := by
  ext a
  rw [Set.mem_ofPred_eq, mem_boundedExponentLists, Set.mem_range]
  constructor
  · intro h
    refine ⟨⟨listExponentVector n a, ?_⟩, ofFn_listExponentVector a h.1⟩
    rw [monomialDegree_listExponentVector a h.1]
    exact h.2
  · rintro ⟨x, rfl⟩
    exact ⟨List.length_ofFn, by simpa only [List.sum_ofFn, monomialDegree] using x.property⟩

/-- Interpret the exponent at a position of the enumeration as a bounded monomial. -/
noncomputable def boundedExponentIndex (D n : ℕ) (i : Fin (boundedExponentLists D n).length) :
    MonomialIndex (Fin n) D := by
  let a := (boundedExponentLists D n).get i
  have ha := (mem_boundedExponentLists D n a).mp (List.get_mem _ _)
  exact ⟨listExponentVector n a, by rw [monomialDegree_listExponentVector a ha.1]; exact ha.2⟩

theorem boundedExponentIndex_bijective (D n : ℕ) :
    Function.Bijective (boundedExponentIndex D n) := by
  constructor
  · intro i j h
    have hi := (mem_boundedExponentLists D n _).mp (List.get_mem (boundedExponentLists D n) i)
    have hj := (mem_boundedExponentLists D n _).mp (List.get_mem (boundedExponentLists D n) j)
    apply (boundedExponentLists_nodup D n).injective_get
    dsimp only [boundedExponentIndex] at h
    have he := congrArg (fun a : MonomialIndex (Fin n) D => List.ofFn a.val) h
    change List.ofFn (listExponentVector n ((boundedExponentLists D n).get i)) =
      List.ofFn (listExponentVector n ((boundedExponentLists D n).get j)) at he
    rwa [ofFn_listExponentVector _ hi.1, ofFn_listExponentVector _ hj.1] at he
  · intro a
    have hm : List.ofFn a.val ∈ boundedExponentLists D n := by
      apply (mem_boundedExponentLists D n _).mpr
      exact ⟨List.length_ofFn, by simpa only [List.sum_ofFn, monomialDegree] using a.property⟩
    obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hm
    refine ⟨⟨i, hi⟩, Subtype.ext ?_⟩
    change listExponentVector n ((boundedExponentLists D n)[i]) = a.val
    rw [he, listExponentVector_ofFn]

theorem boundedExponentLists_length_eq_card (D n : ℕ) :
    (boundedExponentLists D n).length = Fintype.card (MonomialIndex (Fin n) D) := by
  simpa only [Fintype.card_fin] using Fintype.card_congr
    (Equiv.ofBijective _ (boundedExponentIndex_bijective D n))

end PolynomialLift
end ContinuousBilinear
