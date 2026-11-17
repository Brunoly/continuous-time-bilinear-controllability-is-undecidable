import ContinuousBilinear.PolynomialLiftComputableSparse
import ContinuousBilinear.PolynomialLiftComputableCoordinates
import ContinuousBilinear.PolynomialRepresentationProof

namespace ContinuousBilinear
namespace PolynomialLift

open MvPolynomial

namespace SparseCode

noncomputable def denoteOn (n : ℕ) (c : SparseCode) : OscillatorPolynomial n :=
  rename (oscillatorCoordinateEquiv n).symm (denote (3 * n + 1) c)

@[simp] theorem denoteOn_constant (n : ℕ) (c : ℤ) :
    denoteOn n (constant (3 * n + 1) c) = C c := by simp [denoteOn, denote_constant]

@[simp] theorem denoteOn_variableCode (n : ℕ) (x : OscillatorCoordinate n) :
    denoteOn n (variableCode (3 * n + 1) (oscillatorCoordinateNumber x).val) = X x := by
  rw [denoteOn, denote_variableCode, rename_X]
  exact congrArg X ((oscillatorCoordinateEquiv n).symm_apply_apply x)

@[simp] theorem denoteOn_append (n : ℕ) (a b : SparseCode) :
    denoteOn n (a ++ b) = denoteOn n a + denoteOn n b := by simp [denoteOn, denote_append]

@[simp] theorem denoteOn_scale (n : ℕ) (c : ℤ) (a : SparseCode) :
    denoteOn n (scale c a) = C c * denoteOn n a := by simp [denoteOn, denote_scale]

@[simp] theorem denoteOn_mul (n : ℕ) (a b : SparseCode) :
    denoteOn n (mul (3 * n + 1) a b) = denoteOn n a * denoteOn n b := by
  simp [denoteOn, denote_mul]

@[simp] theorem denoteOn_pow (n : ℕ) (a : SparseCode) (k : ℕ) :
    denoteOn n (pow (3 * n + 1) a k) = denoteOn n a ^ k := by simp [denoteOn, denote_pow]

@[simp] theorem denoteOn_product (n : ℕ) (xs : List SparseCode) :
    denoteOn n (product (3 * n + 1) xs) = (xs.map (denoteOn n)).prod := by
  simp [denoteOn, denote_product, map_list_prod, List.map_map, Function.comp_def]
  rfl

@[simp] theorem denoteOn_flatten (n : ℕ) (xs : List SparseCode) :
    denoteOn n xs.flatten = (xs.map (denoteOn n)).sum := by
  simp [denoteOn, denote_flatten, map_list_sum, List.map_map, Function.comp_def]
  rfl

theorem ofFn_val_map_range {α : Type*} (n : ℕ) (f : ℕ → α) :
    List.ofFn (fun i : Fin n => f i.val) = (List.range n).map f := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem denoteOn_sum_range (n k : ℕ) (f : ℕ → SparseCode) :
    denoteOn n ((List.range k).map f).flatten =
      ∑ i : Fin k, denoteOn n (f i.val) := by
  rw [denoteOn_flatten, ← ofFn_val_map_range, List.map_ofFn, List.sum_ofFn]
  rfl

theorem denoteOn_product_range (n k : ℕ) (f : ℕ → SparseCode) :
    denoteOn n (product (3 * n + 1) ((List.range k).map f)) =
      ∏ i : Fin k, denoteOn n (f i.val) := by
  rw [denoteOn_product, ← ofFn_val_map_range, List.map_ofFn, List.prod_ofFn]
  rfl

end SparseCode

def signCoordinateWidth (p : IntegerPolynomialCode) : ℕ := 3 * (p.arity + 1) + 1

def positionCode (p : IntegerPolynomialCode) (i : ℕ) : SparseCode :=
  SparseCode.variableCode (signCoordinateWidth p) (1 + 3 * i)

def sineCode (p : IntegerPolynomialCode) (i : ℕ) : SparseCode :=
  SparseCode.variableCode (signCoordinateWidth p) (1 + 3 * i + 2)

def affineCode (p : IntegerPolynomialCode) : SparseCode :=
  SparseCode.variableCode (signCoordinateWidth p) 0

def signScaleCode (p : IntegerPolynomialCode) : ℤ :=
  2 ^ (p.homogenizingDegreeCode + 1) * (p.homogenizingDegreeCode : ℤ) *
    ((p.coefficientHeightCode : ℤ) + 1)

@[simp] theorem signScaleCode_eq (p : IntegerPolynomialCode) : signScaleCode p = p.signScale := by
  simp [signScaleCode, IntegerPolynomialCode.homogenizingDegreeCode_eq,
    IntegerPolynomialCode.coefficientHeightCode_eq, IntegerPolynomialCode.signScale]

def homogenizedMonomialCode (p : IntegerPolynomialCode) (a : List ℕ) : SparseCode :=
  let n := signCoordinateWidth p
  SparseCode.scale (p.coefficient a) (SparseCode.mul n
    (SparseCode.pow n (positionCode p 0) (p.homogenizingDegreeCode - a.sum))
    (SparseCode.product n ((List.range p.arity).map fun i =>
      SparseCode.pow n (positionCode p (i + 1)) (a.getD i 0))))

def homogenizedPolynomialCode (p : IntegerPolynomialCode) : SparseCode :=
  (p.supportLists.map (homogenizedMonomialCode p)).flatten

def gatePolynomialCode (p : IntegerPolynomialCode) : SparseCode :=
  let n := signCoordinateWidth p
  SparseCode.mul n (positionCode p 0 ++ SparseCode.constant n (-3))
    (SparseCode.constant n 4 ++ SparseCode.scale (-1) (positionCode p 0)) ++
    SparseCode.scale (-1) (SparseCode.pow n (affineCode p) 2)

def squaredCoordinatesCode (p : IntegerPolynomialCode) (f : ℕ → SparseCode) : SparseCode :=
  ((List.range (p.arity + 1)).map fun i => SparseCode.pow (signCoordinateWidth p) (f i) 2).flatten

/-- Integer code for the exact polynomial used by the sign construction. -/
def signPolynomialCode (p : IntegerPolynomialCode) : SparseCode :=
  let n := signCoordinateWidth p
  SparseCode.pow n (homogenizedPolynomialCode p) 2 ++
    SparseCode.mul n
      (SparseCode.mul n (SparseCode.constant n (signScaleCode p ^ 2))
        (SparseCode.pow n (SparseCode.constant n 1 ++ squaredCoordinatesCode p (positionCode p))
          (p.homogenizingDegreeCode - 1)))
      (squaredCoordinatesCode p (sineCode p) ++ SparseCode.pow n (gatePolynomialCode p) 2) ++
    SparseCode.constant n (-1)

@[simp] theorem denoteOn_positionCode (p : IntegerPolynomialCode) (i : Fin (p.arity + 1)) :
    SparseCode.denoteOn (p.arity + 1) (positionCode p i.val) = position (p := p) i := by
  simpa [position, positionCode, signCoordinateWidth, oscillatorCoordinate, oscillatorCoordinateNumber] using
    SparseCode.denoteOn_variableCode (p.arity + 1) (oscillatorCoordinate i 0)

@[simp] theorem denoteOn_sineCode (p : IntegerPolynomialCode) (i : Fin (p.arity + 1)) :
    SparseCode.denoteOn (p.arity + 1) (sineCode p i.val) = sineCoordinate (p := p) i := by
  simpa [sineCoordinate, sineCode, signCoordinateWidth, oscillatorCoordinate, oscillatorCoordinateNumber] using
    SparseCode.denoteOn_variableCode (p.arity + 1) (oscillatorCoordinate i 2)

@[simp] theorem denoteOn_affineCode (p : IntegerPolynomialCode) :
    SparseCode.denoteOn (p.arity + 1) (affineCode p) = affineVariable p :=
  SparseCode.denoteOn_variableCode (p.arity + 1) affineCoordinate

theorem denoteOn_homogenizedMonomialCode (p : IntegerPolynomialCode) (a : List ℕ)
    (ha : a.length = p.arity) :
    SparseCode.denoteOn (p.arity + 1) (homogenizedMonomialCode p a) =
      C (p.denote.coeff (listExponentVector p.arity a)) *
        position (p := p) 0 ^ (p.homogenizingDegree -
          (listExponentVector p.arity a).sum (fun _ e => e)) *
        ∏ i : Fin p.arity, position (p := p) i.succ ^ listExponentVector p.arity a i := by
  rw [homogenizedMonomialCode, signCoordinateWidth, SparseCode.denoteOn_scale,
    SparseCode.denoteOn_mul, SparseCode.denoteOn_pow, SparseCode.denoteOn_product_range,
    IntegerPolynomialCode.coefficient_eq_listExponentVector, IntegerPolynomialCode.homogenizingDegreeCode_eq,
    sum_exponents, monomialDegree_listExponentVector _ ha, mul_assoc]
  have hz := denoteOn_positionCode p 0
  change SparseCode.denoteOn (p.arity + 1) (positionCode p 0) = position (p := p) 0 at hz
  rw [hz]
  congr 1
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp only [SparseCode.denoteOn_pow, listExponentVector_apply]
  rw [← denoteOn_positionCode p i.succ]
  rfl

theorem denoteOn_homogenizedPolynomialCode (p : IntegerPolynomialCode) :
    SparseCode.denoteOn (p.arity + 1) (homogenizedPolynomialCode p) = homogenizedPolynomial p := by
  rw [homogenizedPolynomialCode, SparseCode.denoteOn_flatten, List.map_map, homogenizedPolynomial,
    ← p.supportLists_image, Finset.sum_image]
  · rw [List.sum_toFinset _ (p.supportLists_nodup)]
    congr 1
    apply List.map_congr_left
    intro a ha
    exact denoteOn_homogenizedMonomialCode p a (p.supportLists_length ha)
  · intro a ha b hb he
    have hA := ofFn_listExponentVector a (p.supportLists_length (List.mem_toFinset.mp ha))
    have hB := ofFn_listExponentVector b (p.supportLists_length (List.mem_toFinset.mp hb))
    rw [← hA, ← hB, he]

theorem denoteOn_gatePolynomialCode (p : IntegerPolynomialCode) :
    SparseCode.denoteOn (p.arity + 1) (gatePolynomialCode p) = gatePolynomial p := by
  have hz := denoteOn_positionCode p 0
  change SparseCode.denoteOn (p.arity + 1) (positionCode p 0) = position (p := p) 0 at hz
  simp [gatePolynomialCode, signCoordinateWidth, gatePolynomial, hz, sub_eq_add_neg]

theorem denoteOn_signPolynomialCode (p : IntegerPolynomialCode) :
    SparseCode.denoteOn (p.arity + 1) (signPolynomialCode p) = signPolynomial p := by
  simp only [signPolynomialCode, signCoordinateWidth, SparseCode.denoteOn_append,
    SparseCode.denoteOn_pow, SparseCode.denoteOn_constant, SparseCode.denoteOn_mul,
    denoteOn_gatePolynomialCode, denoteOn_homogenizedPolynomialCode, signScaleCode_eq,
    IntegerPolynomialCode.homogenizingDegreeCode_eq, squaredCoordinatesCode,
    SparseCode.denoteOn_sum_range, denoteOn_positionCode, denoteOn_sineCode]
  simp [signPolynomial, sub_eq_add_neg]

theorem wellSized_signPolynomialCode (p : IntegerPolynomialCode) :
    SparseCode.WellSized (signCoordinateWidth p) (signPolynomialCode p) := by
  unfold signPolynomialCode
  repeat first
    | apply SparseCode.wellSized_append
    | exact SparseCode.wellSized_constant _ _
    | exact SparseCode.wellSized_pow _ _ _
    | exact SparseCode.wellSized_mul _ _ _

namespace SparseCode

theorem primrec_mul_comp {α : Type*} [Primcodable α] {n : α → ℕ} {a b : α → SparseCode}
    (hn : Primrec n) (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun x => mul (n x) (a x) (b x)) :=
  primrec_mul.comp (hn.pair (ha.pair hb))

theorem primrec_pow_comp {α : Type*} [Primcodable α] {n k : α → ℕ} {a : α → SparseCode}
    (hn : Primrec n) (ha : Primrec a) (hk : Primrec k) :
    Primrec (fun x => pow (n x) (a x) (k x)) :=
  primrec_pow.comp (hn.pair (ha.pair hk))

theorem primrec_flatten : Primrec (List.flatten : List SparseCode → SparseCode) :=
  (Primrec.list_flatMap Primrec.id Primrec.snd.to₂).of_eq (fun _ => by simp [List.flatMap])

end SparseCode

theorem primrec_signCoordinateWidth : Primrec signCoordinateWidth :=
  Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 3)
    (Primrec.succ.comp IntegerPolynomialCode.primrec_arity))

private theorem primrec_positionCode : Primrec₂ positionCode :=
  SparseCode.primrec_variableCode.comp₂ (primrec_signCoordinateWidth.comp Primrec.fst).to₂
    ((Primrec.nat_add.comp (Primrec.const 1)
      (Primrec.nat_mul.comp (Primrec.const 3) Primrec.snd)).to₂)

private theorem primrec_sineCode : Primrec₂ sineCode :=
  SparseCode.primrec_variableCode.comp₂ (primrec_signCoordinateWidth.comp Primrec.fst).to₂
    ((Primrec.nat_add.comp
      (Primrec.nat_add.comp (Primrec.const 1) (Primrec.nat_mul.comp (Primrec.const 3)
        Primrec.snd)) (Primrec.const 2)).to₂)

private theorem primrec_affineCode : Primrec affineCode :=
  SparseCode.primrec_variableCode.comp primrec_signCoordinateWidth (Primrec.const 0)

private theorem primrec_signScaleCode : Primrec signScaleCode :=
  IntegerPolynomialCode.primrec_signScale.of_eq (fun p => (signScaleCode_eq p).symm)

private theorem primrec_homogenizedMonomialCode : Primrec₂ homogenizedMonomialCode := by
  apply Primrec₂.curry.mp
  let hwidth := primrec_signCoordinateWidth.comp (Primrec.fst : Primrec
    (Prod.fst : IntegerPolynomialCode × List ℕ → IntegerPolynomialCode))
  let hp := (Primrec.fst.comp Primrec.fst : Primrec
    (fun a : (IntegerPolynomialCode × List ℕ) × ℕ => a.1.1))
  let ha := (Primrec.snd.comp Primrec.fst : Primrec
    (fun a : (IntegerPolynomialCode × List ℕ) × ℕ => a.1.2))
  have hother : Primrec (fun a : IntegerPolynomialCode × List ℕ =>
      ((List.range a.1.arity).map fun i =>
        SparseCode.pow (signCoordinateWidth a.1) (positionCode a.1 (i + 1)) (a.2.getD i 0))) :=
    Primrec.list_map (Primrec.list_range.comp (IntegerPolynomialCode.primrec_arity.comp Primrec.fst))
      ((SparseCode.primrec_pow_comp (hwidth.comp Primrec.fst)
        (primrec_positionCode.comp hp (Primrec.succ.comp Primrec.snd))
        ((Primrec.list_getD 0).comp ha Primrec.snd))).to₂
  exact SparseCode.primrec_scale.comp
    (IntegerPolynomialCode.primrec_coefficient.comp Primrec.fst Primrec.snd)
    (SparseCode.primrec_mul_comp hwidth
      (SparseCode.primrec_pow_comp hwidth
        (primrec_positionCode.comp Primrec.fst (Primrec.const 0))
        (Primrec.nat_sub.comp (IntegerPolynomialCode.primrec_homogenizingDegreeCode.comp Primrec.fst)
          (primrec_nat_listSum.comp Primrec.snd)))
      (SparseCode.primrec_product.comp hwidth hother))

private theorem primrec_homogenizedPolynomialCode : Primrec homogenizedPolynomialCode :=
  SparseCode.primrec_flatten.comp
    (Primrec.list_map IntegerPolynomialCode.primrec_supportLists primrec_homogenizedMonomialCode)

private theorem primrec_gatePolynomialCode : Primrec gatePolynomialCode := by
  let n := primrec_signCoordinateWidth
  let hq := primrec_positionCode.comp Primrec.id (Primrec.const 0)
  let hneg := (Primrec.const (-1 : ℤ) : Primrec (fun _ : IntegerPolynomialCode => (-1 : ℤ)))
  exact Primrec.list_append.comp
    (SparseCode.primrec_mul_comp n
      (Primrec.list_append.comp hq (SparseCode.primrec_constant.comp n (Primrec.const (-3))))
      (Primrec.list_append.comp (SparseCode.primrec_constant.comp n (Primrec.const 4))
        (SparseCode.primrec_scale.comp hneg hq)))
    (SparseCode.primrec_scale.comp hneg
      (SparseCode.primrec_pow_comp n primrec_affineCode (Primrec.const 2)))

private theorem primrec_squaredCoordinatesCode {f : IntegerPolynomialCode → ℕ → SparseCode}
    (hf : Primrec₂ f) : Primrec (fun p => squaredCoordinatesCode p (f p)) :=
  SparseCode.primrec_flatten.comp
    (Primrec.list_map (Primrec.list_range.comp
      (Primrec.succ.comp IntegerPolynomialCode.primrec_arity))
      ((SparseCode.primrec_pow_comp (primrec_signCoordinateWidth.comp Primrec.fst)
        (hf.comp Primrec.fst Primrec.snd) (Primrec.const 2))).to₂)

theorem primrec_signPolynomialCode : Primrec signPolynomialCode := by
  let n := primrec_signCoordinateWidth
  let h2 := (Primrec.const (2 : ℕ) : Primrec (fun _ : IntegerPolynomialCode => (2 : ℕ)))
  let hC {c : IntegerPolynomialCode → ℤ} (hc : Primrec c) :
      Primrec (fun p => SparseCode.constant (signCoordinateWidth p) (c p)) :=
    SparseCode.primrec_constant.comp n hc
  refine Primrec.list_append.comp (Primrec.list_append.comp
    (SparseCode.primrec_pow_comp n primrec_homogenizedPolynomialCode h2)
    (SparseCode.primrec_mul_comp n
      (SparseCode.primrec_mul_comp n
        (hC ((primrec_int_mul.comp primrec_signScaleCode primrec_signScaleCode).of_eq
          (fun p => (pow_two (signScaleCode p)).symm)))
        (SparseCode.primrec_pow_comp n
          (Primrec.list_append.comp (hC (Primrec.const 1))
            (primrec_squaredCoordinatesCode primrec_positionCode))
          (Primrec.pred.comp IntegerPolynomialCode.primrec_homogenizingDegreeCode)))
      (Primrec.list_append.comp
        (primrec_squaredCoordinatesCode primrec_sineCode)
        (SparseCode.primrec_pow_comp n primrec_gatePolynomialCode h2))))
    (hC (Primrec.const (-1)))

end PolynomialLift
end ContinuousBilinear
