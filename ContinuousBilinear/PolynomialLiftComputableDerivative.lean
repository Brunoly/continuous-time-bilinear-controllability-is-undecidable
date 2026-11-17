import ContinuousBilinear.PolynomialLiftComputableSignCode

namespace ContinuousBilinear
namespace PolynomialLift

open MvPolynomial

noncomputable def exponentListOn (n : ℕ) (exps : List ℕ) : OscillatorCoordinate n →₀ ℕ :=
  Finsupp.domCongr (oscillatorCoordinateEquiv n).symm (listExponentVector (3 * n + 1) exps)

@[simp] theorem exponentListOn_apply (n : ℕ) (exps : List ℕ) (z : OscillatorCoordinate n) :
    exponentListOn n exps z = exps.getD (oscillatorCoordinateNumber z).val 0 := by
  simp [exponentListOn]

theorem denoteOn_singleton (n : ℕ) (exps : List ℕ) (c : ℤ) :
    SparseCode.denoteOn n [(c, exps)] = monomial (exponentListOn n exps) c := by
  simp [SparseCode.denoteOn, SparseCode.denote, exponentListOn, rename_monomial,
    Finsupp.domCongr, Finsupp.equivMapDomain_eq_mapDomain]

theorem coeff_denoteOn_eq_sparseCoefficient (n : ℕ) (a : SparseCode)
    (ha : SparseCode.WellSized (3 * n + 1) a) (exps : List ℕ) (he : exps.length = 3 * n + 1) :
    (SparseCode.denoteOn n a).coeff (exponentListOn n exps) = SparseCode.coefficient a exps := by
  unfold SparseCode.denoteOn exponentListOn
  change (rename (oscillatorCoordinateEquiv n).symm (SparseCode.denote (3 * n + 1) a)).coeff
    (Finsupp.equivMapDomain (oscillatorCoordinateEquiv n).symm (listExponentVector (3 * n + 1) exps)) = _
  rw [Finsupp.equivMapDomain_eq_mapDomain, coeff_rename_mapDomain _
    (oscillatorCoordinateEquiv n).symm.injective]
  exact (SparseCode.coefficient_eq_coeff _ _ ha _ he).symm

/-- An integer polynomial code for one component of an oscillator vector field.
Channels and coordinates use the explicit integer indexing from the lift. -/
def oscillatorFieldCode (n channel coordinate : ℕ) : SparseCode :=
  let width := 3 * n + 1
  if channel = 0 then
    if coordinate = 0 then SparseCode.constant width 1 else []
  else
    let q := 1 + 3 * (channel - 1)
    if coordinate = q then SparseCode.constant width 1
    else if coordinate = q + 1 then SparseCode.scale (-1) (SparseCode.variableCode width (q + 2))
    else if coordinate = q + 2 then SparseCode.variableCode width (q + 1)
    else []

theorem denoteOn_oscillatorFieldCode (n : ℕ) (i : Fin (n + 1)) (z : OscillatorCoordinate n) :
    SparseCode.denoteOn n (oscillatorFieldCode n i.val (oscillatorCoordinateNumber z).val) =
      oscillatorField (oscillatorChannelAt n i) z := by
  have hzero : SparseCode.denoteOn n [] = 0 := by simp [SparseCode.denoteOn, SparseCode.denote]
  refine Fin.cases ?_ (fun k => ?_) i
  · rcases z with _ | ⟨j, l⟩
    · simp [oscillatorFieldCode, oscillatorCoordinateNumber, oscillatorField, oscillatorChannelAt_zero]
    · simp [oscillatorFieldCode, oscillatorCoordinateNumber, oscillatorField, hzero]
  · rcases z with _ | ⟨j, l⟩
    · have hne : (0 : ℕ) ≠ 1 + 3 * k.val := by omega
      simp [oscillatorFieldCode, oscillatorCoordinateNumber, oscillatorField, hzero, hne]
    · by_cases h : k = j
      · subst j
        have hc := SparseCode.denoteOn_variableCode n (oscillatorCoordinate k 1)
        have hs := SparseCode.denoteOn_variableCode n (oscillatorCoordinate k 2)
        change SparseCode.denoteOn n (SparseCode.variableCode (3 * n + 1)
          (1 + 3 * k.val + 1)) = X (oscillatorCoordinate k 1) at hc
        change SparseCode.denoteOn n (SparseCode.variableCode (3 * n + 1)
          (1 + 3 * k.val + 2)) = X (oscillatorCoordinate k 2) at hs
        fin_cases l <;> simp [oscillatorFieldCode, oscillatorCoordinateNumber, oscillatorField, hc, hs]
      · have hkj : k.val ≠ j.val := fun h' => h (Fin.ext h')
        have hv0 : 1 + 3 * j.val + l.val ≠ 1 + 3 * k.val := by omega
        have hv1 : 1 + 3 * j.val + l.val ≠ 1 + 3 * k.val + 1 := by omega
        have hv2 : 1 + 3 * j.val + l.val ≠ 1 + 3 * k.val + 2 := by omega
        simp [oscillatorFieldCode, oscillatorCoordinateNumber, oscillatorField, h,
          hv0, hv1, hv2, hzero]

/-- Decrease one exponent, with the zero exponent left at zero. Its derivative coefficient is zero. -/
def decreaseExponentAt (width x : ℕ) (exps : List ℕ) : List ℕ :=
  (List.range width).map fun i => exps.getD i 0 - if i = x then 1 else 0

theorem exponentListOn_decrease (n : ℕ) (exps : List ℕ) (x : OscillatorCoordinate n) :
    exponentListOn n (decreaseExponentAt (3 * n + 1) (oscillatorCoordinateNumber x).val exps) =
      exponentListOn n exps - Finsupp.single x 1 := by
  ext z
  have hlt := (oscillatorCoordinateNumber z).isLt
  have hinj : (oscillatorCoordinateNumber z).val = (oscillatorCoordinateNumber x).val ↔ z = x :=
    ⟨fun h => (oscillatorCoordinateEquiv n).injective (Fin.ext h),
      fun h => congrArg (fun y : OscillatorCoordinate n => (oscillatorCoordinateNumber y).val) h⟩
  simp [decreaseExponentAt, Finsupp.tsub_apply, Finsupp.single_apply, hlt, hinj, eq_comm]

/-- Differentiate the monomial by each coordinate and multiply by the corresponding
component of the vector field. -/
def monomialDerivativeCode (n channel : ℕ) (exps : List ℕ) : SparseCode :=
  let width := 3 * n + 1
  ((List.range width).map fun i =>
    SparseCode.mul width [((exps.getD i 0 : ℤ), decreaseExponentAt width i exps)]
      (oscillatorFieldCode n channel i)).flatten

theorem wellSized_monomialDerivativeCode (n channel : ℕ) (exps : List ℕ) :
    SparseCode.WellSized (3 * n + 1) (monomialDerivativeCode n channel exps) := by
  unfold monomialDerivativeCode
  apply SparseCode.wellSized_flatten
  intro a ha
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp ha
  exact SparseCode.wellSized_mul _ _ _

theorem denoteOn_monomialDerivativeCode (n : ℕ) (i : Fin (n + 1)) (exps : List ℕ) :
    SparseCode.denoteOn n (monomialDerivativeCode n i.val exps) =
      oscillatorDerivation (oscillatorChannelAt n i) (monomial (exponentListOn n exps) 1) := by
  unfold monomialDerivativeCode oscillatorDerivation
  rw [SparseCode.denoteOn_sum_range, mkDerivation_monomial, one_smul]
  rw [Finsupp.sum_fintype _ _ (by intro a; simp)]
  refine Fintype.sum_equiv (oscillatorCoordinateEquiv n).symm _ _ (fun k => ?_)
  have hk : oscillatorCoordinateNumber ((oscillatorCoordinateEquiv n).symm k) = k :=
    (oscillatorCoordinateEquiv n).apply_symm_apply k
  rw [SparseCode.denoteOn_mul, denoteOn_singleton]
  conv_lhs => rw [← hk]
  simp only [denoteOn_oscillatorFieldCode, exponentListOn_decrease, exponentListOn_apply,
    smul_eq_mul]

def monomialDerivativeEntry (n channel : ℕ) (row col : List ℕ) : ℤ :=
  SparseCode.coefficient (monomialDerivativeCode n channel row) col

theorem monomialDerivativeEntry_eq_coeff (n : ℕ) (i : Fin (n + 1)) (row col : List ℕ)
    (hc : col.length = 3 * n + 1) :
    monomialDerivativeEntry n i.val row col =
      (oscillatorDerivation (oscillatorChannelAt n i)
        (monomial (exponentListOn n row) 1)).coeff (exponentListOn n col) := by
  rw [monomialDerivativeEntry, ← coeff_denoteOn_eq_sparseCoefficient n _
    (wellSized_monomialDerivativeCode _ _ _) col hc, denoteOn_monomialDerivativeCode]

theorem primrec_oscillatorFieldCode :
    Primrec (fun p : ℕ × ℕ × ℕ => oscillatorFieldCode p.1 p.2.1 p.2.2) := by
  let w := Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 3)
    (Primrec.fst : Primrec (Prod.fst : ℕ × ℕ × ℕ → ℕ)))
  let chan := (Primrec.fst.comp Primrec.snd : Primrec (fun p : ℕ × ℕ × ℕ => p.2.1))
  let x := (Primrec.snd.comp Primrec.snd : Primrec (fun p : ℕ × ℕ × ℕ => p.2.2))
  let q := Primrec.nat_add.comp (Primrec.const 1)
    (Primrec.nat_mul.comp (Primrec.const 3) (Primrec.nat_sub.comp chan (Primrec.const 1)))
  let one := SparseCode.primrec_constant.comp w (Primrec.const 1)
  let hnil := (Primrec.const ([] : SparseCode) : Primrec (fun _ : ℕ × ℕ × ℕ => ([] : SparseCode)))
  exact Primrec.ite (Primrec.eq.comp chan (Primrec.const 0))
    (Primrec.ite (Primrec.eq.comp x (Primrec.const 0)) one hnil)
    (Primrec.ite (Primrec.eq.comp x q) one
      (Primrec.ite (Primrec.eq.comp x (Primrec.succ.comp q))
        (SparseCode.primrec_scale.comp (Primrec.const (-1))
          (SparseCode.primrec_variableCode.comp w
            (Primrec.nat_add.comp q (Primrec.const 2))))
        (Primrec.ite (Primrec.eq.comp x (Primrec.nat_add.comp q (Primrec.const 2)))
          (SparseCode.primrec_variableCode.comp w (Primrec.succ.comp q)) hnil)))

theorem primrec_decreaseExponentAt :
    Primrec (fun p : ℕ × ℕ × List ℕ => decreaseExponentAt p.1 p.2.1 p.2.2) := by
  exact Primrec.list_map (Primrec.list_range.comp Primrec.fst)
    ((Primrec.nat_sub.comp
      ((Primrec.list_getD 0).comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
      (Primrec.ite (Primrec.eq.comp Primrec.snd
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
        (Primrec.const 1) (Primrec.const 0)))).to₂

theorem primrec_monomialDerivativeCode :
    Primrec (fun p : ℕ × ℕ × List ℕ => monomialDerivativeCode p.1 p.2.1 p.2.2) := by
  let width := Primrec.succ.comp (Primrec.nat_mul.comp (Primrec.const 3)
    (Primrec.fst : Primrec (Prod.fst : ℕ × ℕ × List ℕ → ℕ)))
  have hrow : Primrec (fun a : (ℕ × ℕ × List ℕ) × ℕ =>
      [((a.1.2.2.getD a.2 0 : ℤ), decreaseExponentAt (3 * a.1.1 + 1) a.2 a.1.2.2)]) :=
    Primrec.list_cons.comp ((primrec_int_ofNat.comp ((Primrec.list_getD 0).comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)).pair
      (primrec_decreaseExponentAt.comp ((width.comp Primrec.fst).pair
        (Primrec.snd.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))))
      (Primrec.const [])
  have hfield : Primrec (fun a : (ℕ × ℕ × List ℕ) × ℕ => oscillatorFieldCode a.1.1 a.1.2.1 a.2) :=
    primrec_oscillatorFieldCode.comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd))
  exact SparseCode.primrec_flatten.comp
    (Primrec.list_map (Primrec.list_range.comp width)
      (SparseCode.primrec_mul_comp (width.comp Primrec.fst) hrow hfield).to₂)

theorem primrec_monomialDerivativeEntry :
    Primrec (fun p : ℕ × ℕ × List ℕ × List ℕ =>
      monomialDerivativeEntry p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  SparseCode.primrec_coefficient.comp
    (primrec_monomialDerivativeCode.comp (Primrec.fst.pair
      ((Primrec.fst.comp Primrec.snd).pair
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

end PolynomialLift
end ContinuousBilinear
