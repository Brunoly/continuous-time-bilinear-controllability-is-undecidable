import ContinuousBilinear.PolynomialLiftQuotientDynamics

namespace ContinuousBilinear
namespace PolynomialLift
namespace LinearRepresentation

open Module
open scoped BigOperators Matrix

noncomputable section

variable {V W ι : Type*} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W] {n m : ℕ}

def coordinateOperators (F : LinearRepresentation ℚ V ι) (b : Basis (Fin n) ℚ V)
    (i : ι) : Matrix (Fin n) (Fin n) ℚ :=
  LinearMap.toMatrix b b (F.operator i)

def realCoordinates (b : Basis (Fin n) ℚ V) (x : V) : State n :=
  fun j => (b.repr x j : ℝ)

def realOutput (F : LinearRepresentation ℚ V ι) (b : Basis (Fin n) ℚ V)
    (x : State n) : ℝ :=
  ∑ j, (F.output (b j) : ℝ) * x j

def exponentialCoefficient [Fintype ι] (F : LinearRepresentation ℚ V ι)
    (b : Basis (Fin n) ℚ V) (u : ι → ℝ) : ℝ :=
  realOutput F b ((NormedSpace.exp (realPencil (coordinateOperators F b) u)).mulVec
    (realCoordinates b F.initial))

private theorem output_columns (f : V →ₗ[ℚ] W) (out : W →ₗ[ℚ] ℚ)
    (b : Basis (Fin n) ℚ V) (c : Basis (Fin m) ℚ W) (j : Fin n) :
    (∑ k, out (c k) * LinearMap.toMatrix b c f k j) = out (f (b j)) := by
  have h := congrArg out (c.sum_repr (f (b j)))
  simp only [map_sum, map_smul, smul_eq_mul] at h
  simpa only [LinearMap.toMatrix_apply, mul_comm] using h

theorem realCoordinates_map (f : V →ₗ[ℚ] W)
    (b : Basis (Fin n) ℚ V) (c : Basis (Fin m) ℚ W) (x : V) :
    ((LinearMap.toMatrix b c f).map (Rat.castHom ℝ)).mulVec (realCoordinates b x) =
      realCoordinates c (f x) := by
  funext i
  change _ = (Rat.castHom ℝ) (c.repr (f x) i)
  rw [← LinearMap.toMatrix_mulVec_repr b c]
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply,
    realCoordinates, Rat.coe_castHom]

theorem realOutput_map (F : LinearRepresentation ℚ V ι)
    (G : LinearRepresentation ℚ W ι) (f : V →ₗ[ℚ] W)
    (b : Basis (Fin n) ℚ V) (c : Basis (Fin m) ℚ W)
    (hout : ∀ x, G.output (f x) = F.output x) (x : State n) :
    realOutput G c (((LinearMap.toMatrix b c f).map (Rat.castHom ℝ)).mulVec x) =
      realOutput F b x := by
  unfold realOutput
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Finset.sum_mul]
  congr 1
  have h := congrArg (Rat.castHom ℝ) (output_columns f G.output b c j)
  simpa only [map_sum, map_mul, hout, Rat.coe_castHom] using h

theorem exponentialCoefficient_map [Fintype ι]
    (F : LinearRepresentation ℚ V ι) (G : LinearRepresentation ℚ W ι)
    (f : V →ₗ[ℚ] W)
    (b : Basis (Fin n) ℚ V) (c : Basis (Fin m) ℚ W)
    (hinit : f F.initial = G.initial)
    (hout : ∀ x, G.output (f x) = F.output x)
    (hcomm : ∀ i x, f (F.operator i x) = G.operator i (f x)) (u : ι → ℝ) :
    exponentialCoefficient G c u = exponentialCoefficient F b u := by
  let L := LinearMap.toMatrix b c f
  have hmat i : L * coordinateOperators F b i = coordinateOperators G c i * L := by
    dsimp only [L, coordinateOperators]
    rw [← LinearMap.toMatrix_comp, ← LinearMap.toMatrix_comp]
    congr 1
    ext x
    exact hcomm i x
  have he := exp_realPencil_mulVec_intertwining (coordinateOperators F b)
    (coordinateOperators G c) L hmat u (realCoordinates b F.initial)
  change _ = (NormedSpace.exp (realPencil (coordinateOperators G c) u)).mulVec
    (((LinearMap.toMatrix b c f).map (Rat.castHom ℝ)).mulVec (realCoordinates b F.initial)) at he
  rw [realCoordinates_map, hinit] at he
  unfold exponentialCoefficient
  rw [← he]
  exact realOutput_map F G f b c hout _

/-- Reachability restriction followed by the unobservable quotient preserves the
complete exponential scalar coefficient after extending the rational matrices to the reals. -/
theorem minimal_exponentialCoefficient_eq [Fintype ι] [FiniteDimensional ℚ V]
    (F : LinearRepresentation ℚ V ι)
    (b : Basis (Fin n) ℚ V)
    (c : Basis (Fin m) ℚ (F.reachable ⧸ F.unobservable)) (u : ι → ℝ) :
    exponentialCoefficient F.minimalRepresentation c u = exponentialCoefficient F b u := by
  let r := Module.finBasis ℚ F.reachable
  calc
    _ = exponentialCoefficient F.reachableRepresentation r u := by
      exact exponentialCoefficient_map F.reachableRepresentation F.minimalRepresentation
        F.unobservable.mkQ r c rfl (fun _ => rfl) (fun _ _ => rfl) u
    _ = _ := by
      symm
      exact exponentialCoefficient_map F.reachableRepresentation F
        F.reachable.subtype r b rfl (fun _ => rfl) (fun _ _ => rfl) u

end
end LinearRepresentation
end PolynomialLift
end ContinuousBilinear
