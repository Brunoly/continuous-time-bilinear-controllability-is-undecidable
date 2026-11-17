import ContinuousBilinear.PolynomialLiftOscillator
import ContinuousBilinear.PolynomialLiftComputableExponents
import Mathlib.Algebra.MvPolynomial.Rename

namespace ContinuousBilinear
namespace PolynomialLift

/-- Index 0 is the affine coordinate and each oscillator uses three subsequent indices. -/
def oscillatorCoordinateNumber {n : ℕ} : OscillatorCoordinate n → Fin (3 * n + 1)
  | .inl _ => 0
  | .inr (i, k) => ⟨1 + 3 * i.val + k.val, by omega⟩

private theorem oscillatorCoordinateNumber_bijective (n : ℕ) :
    Function.Bijective (oscillatorCoordinateNumber (n := n)) := by
  constructor
  · intro a b h
    have hv := congrArg Fin.val h
    rcases a with ⟨⟩ | ⟨i, k⟩ <;> rcases b with ⟨⟩ | ⟨j, l⟩
    · rfl
    · dsimp [oscillatorCoordinateNumber] at hv
      omega
    · dsimp [oscillatorCoordinateNumber] at hv
      omega
    · dsimp [oscillatorCoordinateNumber] at hv
      have ei : i.val = j.val := by omega
      have ek : k.val = l.val := by omega
      exact congrArg Sum.inr (Prod.ext (Fin.ext ei) (Fin.ext ek))
  · intro i
    by_cases hi : i.val = 0
    · exact ⟨Sum.inl (), Fin.ext hi.symm⟩
    · let j : Fin n := ⟨(i.val - 1) / 3, by omega⟩
      let k : Fin 3 := ⟨(i.val - 1) % 3, by omega⟩
      refine ⟨Sum.inr (j, k), Fin.ext ?_⟩
      change 1 + 3 * ((i.val - 1) / 3) + (i.val - 1) % 3 = i.val
      omega

noncomputable def oscillatorCoordinateEquiv (n : ℕ) :
    OscillatorCoordinate n ≃ Fin (3 * n + 1) :=
  Equiv.ofBijective _ (oscillatorCoordinateNumber_bijective n)

@[simp] theorem oscillatorCoordinateEquiv_apply {n : ℕ} (z : OscillatorCoordinate n) :
    oscillatorCoordinateEquiv n z = oscillatorCoordinateNumber z := rfl

/-- Index 0 acts on the affine coordinate and index i+1 on oscillator i. -/
def oscillatorChannelAt (n : ℕ) : Fin (n + 1) ≃ OscillatorChannel n where
  toFun := Fin.cases none some
  invFun c := c.elim 0 Fin.succ
  left_inv i := Fin.cases (by simp) (fun j => by simp) i
  right_inv c := by cases c <;> simp

@[simp] theorem oscillatorChannelAt_zero (n : ℕ) : oscillatorChannelAt n 0 = none := rfl

@[simp] theorem oscillatorChannelAt_succ (n : ℕ) (j : Fin n) :
    oscillatorChannelAt n j.succ = some j := rfl

theorem monomialDegree_domCongr {σ τ : Type*} [Fintype σ] [Fintype τ]
    (e : σ ≃ τ) (a : σ →₀ ℕ) :
    monomialDegree (Finsupp.domCongr e a) = monomialDegree a := by
  unfold monomialDegree
  exact Fintype.sum_equiv e.symm _ _ (fun j => by simp)

noncomputable def monomialIndexCongr {σ τ : Type*} [Fintype σ] [Fintype τ]
    (D : ℕ) (e : σ ≃ τ) : MonomialIndex σ D ≃ MonomialIndex τ D where
  toFun a := ⟨Finsupp.domCongr e a.val, (monomialDegree_domCongr e a.val).trans_le a.property⟩
  invFun a := ⟨Finsupp.domCongr e.symm a.val,
    (monomialDegree_domCongr e.symm a.val).trans_le a.property⟩
  left_inv a := Subtype.ext (by ext i; simp)
  right_inv a := Subtype.ext (by ext i; simp)

noncomputable def oscillatorExponentIndex (D n : ℕ) :
    Fin (boundedExponentLists D (3 * n + 1)).length ≃ MonomialIndex (OscillatorCoordinate n) D :=
  (Equiv.ofBijective _ (boundedExponentIndex_bijective D (3 * n + 1))).trans
    (monomialIndexCongr D (oscillatorCoordinateEquiv n).symm)

theorem oscillatorExponentIndex_apply (D n : ℕ)
    (i : Fin (boundedExponentLists D (3 * n + 1)).length) (x : OscillatorCoordinate n) :
    (oscillatorExponentIndex D n i).val x =
      ((boundedExponentLists D (3 * n + 1)).get i).getD (oscillatorCoordinateNumber x).val 0 := by
  change (Finsupp.domCongr (oscillatorCoordinateEquiv n).symm
    (listExponentVector (3 * n + 1) ((boundedExponentLists D (3 * n + 1)).get i))) x = _
  simp

end PolynomialLift
end ContinuousBilinear
