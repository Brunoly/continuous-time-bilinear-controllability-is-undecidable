import ContinuousBilinear.PolynomialLiftComputableExponents
import ContinuousBilinear.PolynomialCodeCoefficients

namespace ContinuousBilinear
namespace IntegerPolynomialCode

open MvPolynomial PolynomialLift

theorem primrec_arity : Primrec arity :=
  Primrec.list_foldr (Primrec.list_map Primrec.id (Primrec.list_length.comp (Primrec.snd.comp
    Primrec.snd)).to₂) (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

private theorem primrec_int_listSum : Primrec (List.sum : List ℤ → ℤ) := by
  exact (Primrec.list_foldr Primrec.id (Primrec.const 0)
    (primrec_int_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
      (fun a => by simp [List.sum_eq_foldr])

theorem primrec_coefficient : Primrec₂ coefficient := by
  let P := (IntegerPolynomialCode × List ℕ) × (ℤ × List ℕ)
  let R (i : ℕ) (a : P) : Prop := a.2.2.getD i 0 = a.1.2.getD i 0
  have hR : PrimrecRel R :=
    Primrec.eq.comp
      ((Primrec.list_getD 0).comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)) Primrec.fst)
      ((Primrec.list_getD 0).comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)) Primrec.fst)
  have hcheck : PrimrecPred (fun a : P => (List.range a.1.1.arity).all
      (fun i => a.2.2.getD i 0 == a.1.2.getD i 0) = true) :=
    (hR.forall_mem_list.comp (Primrec.list_range.comp
      (primrec_arity.comp (Primrec.fst.comp Primrec.fst))) Primrec.id).of_eq
        (fun a => by simp [List.all_eq_true, R])
  apply Primrec₂.curry.mp
  exact primrec_int_listSum.comp (Primrec.list_map (Primrec.fst : Primrec
    (Prod.fst : IntegerPolynomialCode × List ℕ → IntegerPolynomialCode))
    (Primrec.ite hcheck (Primrec.fst.comp Primrec.snd) (Primrec.const 0)).to₂)

/-- Maximum coordinate exponent present in the input list before collecting terms. -/
def exponentBound (p : IntegerPolynomialCode) : ℕ :=
  (p.flatMap Prod.snd).foldr max 0

theorem primrec_exponentBound : Primrec exponentBound :=
  Primrec.list_foldr (Primrec.list_flatMap Primrec.id (Primrec.snd.comp Primrec.snd).to₂)
    (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

private theorem le_foldr_max_of_mem (l : List ℕ) (v : ℕ) (h : v ∈ l) :
    v ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

private theorem getD_le_exponentBound (p : IntegerPolynomialCode) (term : ℤ × List ℕ)
    (ht : term ∈ p) (i : ℕ) : term.2.getD i 0 ≤ p.exponentBound := by
  by_cases hi : i < term.2.length
  · rw [listGetD_of_lt _ _ hi]
    exact le_foldr_max_of_mem _ _ (List.mem_flatMap.mpr ⟨term, ht, List.getElem_mem hi⟩)
  · rw [listGetD_of_ge _ _ (Nat.le_of_not_gt hi)]
    exact Nat.zero_le _

/-- Canonical exponent lists with a nonzero combined coefficient. -/
def supportLists (p : IntegerPolynomialCode) : List (List ℕ) :=
  (boxExponentLists p.exponentBound p.arity).filter fun a => p.coefficient a ≠ 0

theorem primrec_supportLists : Primrec supportLists := by
  have hcoeff : Primrec (fun ap : List ℕ × IntegerPolynomialCode => ap.2.coefficient ap.1) :=
    primrec_coefficient.comp Primrec.snd Primrec.fst
  have htest : PrimrecRel (fun (a : List ℕ) (p : IntegerPolynomialCode) =>
      p.coefficient a ≠ 0) := (Primrec.eq.comp hcoeff (Primrec.const 0)).not
  exact htest.listFilter.comp (primrec_boxExponentLists.comp primrec_exponentBound primrec_arity)
    Primrec.id

theorem supportLists_nodup (p : IntegerPolynomialCode) : p.supportLists.Nodup :=
  (boxExponentLists_nodup _ _).filter _

theorem supportLists_length (p : IntegerPolynomialCode) {a : List ℕ} (ha : a ∈ p.supportLists) :
    a.length = p.arity :=
  (mem_boxExponentLists _ _ _ |>.mp (List.mem_filter.mp ha).1).1

private theorem exists_term_of_coefficient_ne_zero (p : IntegerPolynomialCode) (a : List ℕ)
    (h : p.coefficient a ≠ 0) : ∃ term ∈ p, ∀ i < p.arity, term.2.getD i 0 = a.getD i 0 := by
  by_contra! hn
  apply h
  unfold coefficient
  have hmap : (p.map fun term => if (List.range p.arity).all
      (fun i => term.2.getD i 0 == a.getD i 0) then term.1 else 0) = p.map (fun _ => 0) := by
    apply List.map_congr_left
    intro term ht
    have hfalse : (List.range p.arity).all (fun i => term.2.getD i 0 == a.getD i 0) = false := by
      apply Bool.eq_false_iff.mpr
      intro htrue
      obtain ⟨i, hi, hne⟩ := hn term ht
      exact hne (beq_iff_eq.mp ((List.all_eq_true.mp htrue) i (List.mem_range.mpr hi)))
    change (if (List.range p.arity).all (fun i => term.2.getD i 0 == a.getD i 0)
      then term.1 else 0) = 0
    rw [hfalse]
    rfl
  rw [hmap]
  simp

theorem coefficient_eq_listExponentVector (p : IntegerPolynomialCode) (a : List ℕ) :
    p.coefficient a = p.denote.coeff (listExponentVector p.arity a) :=
  coefficient_eq_coeff p a

theorem supportLists_exact (p : IntegerPolynomialCode) (a : List ℕ) :
    a ∈ p.supportLists ↔ a.length = p.arity ∧ listExponentVector p.arity a ∈ p.denote.support := by
  rw [supportLists, List.mem_filter, decide_eq_true_eq, mem_boxExponentLists]
  constructor
  · rintro ⟨⟨hlen, _⟩, hc⟩
    exact ⟨hlen, mem_support_iff.mpr ((p.coefficient_eq_listExponentVector a) ▸ hc)⟩
  · rintro ⟨hlen, hmem⟩
    have hc : p.coefficient a ≠ 0 := (p.coefficient_eq_listExponentVector a).symm ▸
      (mem_support_iff.mp hmem)
    refine ⟨⟨hlen, ?_⟩, hc⟩
    intro v hmem
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hmem
    obtain ⟨term, ht, hterm⟩ := exists_term_of_coefficient_ne_zero p a hc
    rw [← listGetD_of_lt _ _ hk, ← hterm k (hlen ▸ hk)]
    exact getD_le_exponentBound p term ht k

theorem supportLists_image (p : IntegerPolynomialCode) :
    p.supportLists.toFinset.image (listExponentVector p.arity) = p.denote.support := by
  ext a
  rw [Finset.mem_image]
  constructor
  · rintro ⟨l, hl, rfl⟩
    exact ((supportLists_exact p l).mp (List.mem_toFinset.mp hl)).2
  · intro ha
    refine ⟨List.ofFn a, List.mem_toFinset.mpr ?_, listExponentVector_ofFn a⟩
    apply (supportLists_exact p _).mpr
    simp [ha]

def homogenizingDegreeCode (p : IntegerPolynomialCode) : ℕ :=
  max 1 ((p.supportLists.map List.sum).foldr max 0)

private theorem max_foldr_map_eq_sup {α : Type*} [DecidableEq α] (l : List α) (f : α → ℕ) :
    (l.map f).foldr max 0 = l.toFinset.sup f := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Finset.sup_insert]

theorem homogenizingDegreeCode_eq (p : IntegerPolynomialCode) :
    p.homogenizingDegreeCode = p.homogenizingDegree := by
  unfold homogenizingDegreeCode homogenizingDegree MvPolynomial.totalDegree
  rw [max_foldr_map_eq_sup, ← supportLists_image, Finset.sup_image]
  congr 1
  apply Finset.sup_congr rfl
  intro a ha
  dsimp only [Function.comp_apply]
  rw [sum_exponents, monomialDegree_listExponentVector a
    (supportLists_length p (List.mem_toFinset.mp ha))]

theorem primrec_homogenizingDegreeCode : Primrec homogenizingDegreeCode :=
  Primrec.nat_max.comp (Primrec.const 1)
    (Primrec.list_foldr (Primrec.list_map primrec_supportLists
      (primrec_nat_listSum.comp Primrec.snd).to₂) (Primrec.const 0)
      (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂)

def coefficientHeightCode (p : IntegerPolynomialCode) : ℕ :=
  (p.supportLists.map fun a => (p.coefficient a).natAbs).sum

theorem coefficientHeightCode_eq (p : IntegerPolynomialCode) :
    (p.coefficientHeightCode : ℤ) = p.coefficientHeight := by
  unfold coefficientHeightCode coefficientHeight
  rw [← supportLists_image, Finset.sum_image]
  · rw [List.sum_toFinset _ (supportLists_nodup p)]
    simp only [Nat.cast_list_sum, List.map_map]
    apply congrArg List.sum
    apply List.map_congr_left
    intro a _
    simp only [Function.comp_apply, coefficient_eq_listExponentVector, Int.natCast_natAbs]
  · intro a ha b hb he
    have hA := ofFn_listExponentVector a (supportLists_length p (List.mem_toFinset.mp ha))
    have hB := ofFn_listExponentVector b (supportLists_length p (List.mem_toFinset.mp hb))
    rw [← hA, ← hB, he]

theorem primrec_coefficientHeightCode : Primrec coefficientHeightCode :=
  primrec_nat_listSum.comp (Primrec.list_map primrec_supportLists
    (primrec_int_natAbs.comp
      (primrec_coefficient.comp Primrec.fst Primrec.snd)).to₂)

/-- The exact degree used in the analytic sign lemma is primitive recursive on the input code. -/
theorem primrec_homogenizingDegree : Primrec homogenizingDegree :=
  primrec_homogenizingDegreeCode.of_eq homogenizingDegreeCode_eq

/-- The exact coefficient height used in the analytic sign lemma is primitive recursive. -/
theorem primrec_coefficientHeight : Primrec coefficientHeight :=
  (primrec_int_ofNat.comp primrec_coefficientHeightCode).of_eq coefficientHeightCode_eq

private theorem primrec_two_pow : Primrec (fun n : ℕ => (2 : ℕ) ^ n) := by
  have h : Primrec₂ (fun (_ : ℕ) (a : ℕ) => a * 2) :=
    Primrec.nat_mul.comp Primrec.snd (Primrec.const 2)
  refine (Primrec.nat_rec₁ 1 h).of_eq ?_
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ]
    exact congrArg (fun a => a * 2) ih

theorem primrec_signScale : Primrec signScale := by
  have hp : Primrec (fun p : IntegerPolynomialCode => (2 : ℤ) ^ (p.homogenizingDegree + 1)) := by
    refine (primrec_int_ofNat.comp (primrec_two_pow.comp
      (Primrec.succ.comp primrec_homogenizingDegree))).of_eq ?_
    intro p
    simp
  exact primrec_int_mul.comp
    (primrec_int_mul.comp hp (primrec_int_ofNat.comp primrec_homogenizingDegree))
    (primrec_int_add.comp primrec_coefficientHeight (Primrec.const 1))

end IntegerPolynomialCode
end ContinuousBilinear
