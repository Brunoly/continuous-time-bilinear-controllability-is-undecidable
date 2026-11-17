import ContinuousBilinear.CompilerWordOutputProof
import ContinuousBilinear.PolynomialLiftQuotientCoordinates

namespace ContinuousBilinear.PolynomialLift.LinearRepresentation

open Module

noncomputable section

variable {V W ι : Type*} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W] [Fintype ι] {n m : ℕ}

/-- A representation with vanishing word coefficients has identically zero
exponential coefficient. -/
theorem exponentialCoefficient_eq_zero_of_words [FiniteDimensional ℚ V]
    (F : LinearRepresentation ℚ V ι) (b : Basis (Fin n) ℚ V) (u : ι → ℝ)
    (h : ∀ w, F.output (F.wordAction w F.initial) = 0) :
    F.exponentialCoefficient b u = 0 := by
  let B := Module.finBasis ℚ F.reachable
  have he := exponentialCoefficient_map F.reachableRepresentation F
    F.reachable.subtype B b rfl (fun _ => rfl) (fun _ _ => rfl) u
  have hker : F.reachable ≤ LinearMap.ker F.output := by
    apply Submodule.span_le.mpr
    rintro _ ⟨w, rfl⟩
    exact LinearMap.mem_ker.mpr (h w)
  have hout (x : F.reachable) : F.reachableRepresentation.output x = 0 :=
    LinearMap.mem_ker.mp (hker x.property)
  rw [he]
  simp only [exponentialCoefficient, realOutput, hout, Rat.cast_zero, zero_mul, Finset.sum_const_zero]

/-- Equality of rational word coefficients implies equality of the real exponential
coefficients, with no choice of basis built into the assertion. -/
theorem exponentialCoefficient_eq_of_words [FiniteDimensional ℚ V] [FiniteDimensional ℚ W]
    (F : LinearRepresentation ℚ V ι) (G : LinearRepresentation ℚ W ι)
    (b : Basis (Fin n) ℚ V) (c : Basis (Fin m) ℚ W) (u : ι → ℝ)
    (h : ∀ w, F.output (F.wordAction w F.initial) = G.output (G.wordAction w G.initial)) :
    F.exponentialCoefficient b u = G.exponentialCoefficient c u := by
  let D := F.difference G
  let E : LinearRepresentation ℚ (V × W) ι :=
    { D with output := F.output.comp (LinearMap.fst ℚ V W) }
  let H : LinearRepresentation ℚ (V × W) ι :=
    { D with output := G.output.comp (LinearMap.snd ℚ V W) }
  let B := Module.finBasis ℚ (V × W)
  have he := exponentialCoefficient_map E F (LinearMap.fst ℚ V W) B b rfl
    (fun _ => rfl) (fun _ _ => rfl) u
  have hh := exponentialCoefficient_map H G (LinearMap.snd ℚ V W) B c rfl
    (fun _ => rfl) (fun _ _ => rfl) u
  have hzero : D.exponentialCoefficient B u = 0 := by
    apply exponentialCoefficient_eq_zero_of_words
    intro w
    exact (difference_wordOutput F G w).trans (sub_eq_zero.mpr (h w))
  have hsub : D.exponentialCoefficient B u =
      E.exponentialCoefficient B u - H.exponentialCoefficient B u := by
    let x := (NormedSpace.exp (realPencil (D.coordinateOperators B) u)).mulVec
      (realCoordinates B D.initial)
    change D.realOutput B x = E.realOutput B x - H.realOutput B x
    unfold realOutput
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    change (((F.output (B j).1 - G.output (B j).2 : ℚ) : ℝ) * x j) =
      (F.output (B j).1 : ℝ) * x j - (G.output (B j).2 : ℝ) * x j
    rw [Rat.cast_sub, sub_mul]
  rw [he, hh]
  exact sub_eq_zero.mp (hsub.symm.trans hzero)

end
end ContinuousBilinear.PolynomialLift.LinearRepresentation
