import ContinuousBilinear.PolynomialLiftQuotientOrbit
import ContinuousBilinear.Feedback

namespace ContinuousBilinear
namespace PolynomialLift

open scoped BigOperators Matrix
open Module

noncomputable section

namespace LinearRepresentation

variable {V ι : Type*} [AddCommGroup V] [Module ℚ V] {d m : ℕ}

def feedbackData (F : LinearRepresentation ℚ V ι) (b : Basis (Fin d) ℚ V) (e : Fin m ≃ ι) :
    FeedbackData d m where
  K i := F.realOperators b (e i)
  b := realCoordinates b F.initial
  ell := realRow b F.output

private theorem cast_coefficients (F : LinearRepresentation ℚ V ι) (b : Basis (Fin d) ℚ V)
    (x : V) : realOutput F b (realCoordinates b x) = (F.output x : ℝ) := by
  have h := congrArg F.output (b.sum_repr x)
  simp only [map_sum, map_smul, smul_eq_mul] at h
  have h' := congrArg (Rat.castHom ℝ) h
  simpa only [realOutput, realCoordinates, map_sum, map_mul, Rat.coe_castHom, mul_comm] using h'

theorem feedbackData_orbitMatrix [Fintype ι] (F : LinearRepresentation ℚ V ι)
    (b : Basis (Fin d) ℚ V) (e : Fin m ≃ ι) (u : Fin m → ℝ) :
    (F.feedbackData b e).orbitMatrix u =
      NormedSpace.exp (realPencil (F.coordinateOperators b) (u ∘ e.symm)) := by
  apply congrArg NormedSpace.exp
  unfold feedbackData realPencil realOperators
  exact Fintype.sum_equiv e _ _ (fun i => by simp)

theorem feedbackData_hypotheses [Fintype ι] (F : LinearRepresentation ℚ V ι)
    (b : Basis (Fin d) ℚ V) (e : Fin m ≃ ι)
    (hc : ∀ i j, Commute (F.operator i) (F.operator j)) (hinit : F.output F.initial = 1)
    (hcol : F.reachable = ⊤)
    (hrow : Submodule.span ℚ (Set.range fun w : List ι => F.output.comp (F.wordAction w)) = ⊤) :
    (F.feedbackData b e).Hypotheses := by
  let G := F.feedbackData b e
  have hsurj : Function.Surjective (fun u : Fin m → ℝ => u ∘ e.symm) := by
    intro t
    exact ⟨t ∘ e, funext (fun i => by simp)⟩
  have hreindex (f : (ι → ℝ) → State d) :
      Set.range (fun u : Fin m → ℝ => f (u ∘ e.symm)) = Set.range f := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨u ∘ e.symm, rfl⟩
    · rintro ⟨t, rfl⟩
      obtain ⟨u, hu⟩ := hsurj t
      exact ⟨u, congrArg f hu⟩
  refine ⟨fun i j => F.realOperators_commute b hc (e i) (e j), ?_, ?_, ?_⟩
  · change realOutput F b (realCoordinates b F.initial) = 1
    rw [cast_coefficients, hinit, Rat.cast_one]
  · have hspan := F.exponential_columns_span b hc hcol
    change Submodule.span ℝ (Set.range fun u => (G.orbitMatrix u).mulVec G.b) = ⊤
    have he (u : Fin m → ℝ) : (G.orbitMatrix u).mulVec G.b =
        (NormedSpace.exp (∑ i, (u ∘ e.symm) i • F.realOperators b i)).mulVec
          (realCoordinates b F.initial) := by
      dsimp only [G]
      rw [feedbackData_orbitMatrix]
      rfl
    rw [funext he, hreindex (fun v =>
      (NormedSpace.exp (∑ i, v i • F.realOperators b i)).mulVec (realCoordinates b F.initial))]
    exact hspan
  · have hspan := F.exponential_rows_transpose_span b hc hrow
    change Submodule.span ℝ (Set.range fun u : Fin m → ℝ =>
      fun j : Fin d => ∑ i, G.ell i * G.orbitMatrix u i j) = ⊤
    have he (u : Fin m → ℝ) :
        (fun j : Fin d => ∑ i, G.ell i * G.orbitMatrix u i j) =
          (NormedSpace.exp (∑ i, (u ∘ e.symm) i • (F.realOperators b i).transpose)).mulVec
            (realRow b F.output) := by
      have hT : (∑ i, (u ∘ e.symm) i • (F.realOperators b i).transpose) =
          (∑ i, (u ∘ e.symm) i • F.realOperators b i).transpose := by
        rw [Matrix.transpose_sum]
        simp only [Matrix.transpose_smul]
      rw [hT, Matrix.exp_transpose]
      funext j
      dsimp only [G]
      rw [feedbackData_orbitMatrix]
      simp [feedbackData, realPencil, realOperators, Matrix.mulVec, dotProduct, mul_comm]
    rw [funext he, hreindex (fun v =>
      (NormedSpace.exp (∑ i, v i • (F.realOperators b i).transpose)).mulVec (realRow b F.output))]
    exact hspan

theorem feedbackData_negative_iff [Fintype ι] (F : LinearRepresentation ℚ V ι)
    (b : Basis (Fin d) ℚ V) (e : Fin m ≃ ι) :
    (F.feedbackData b e).HasNegativePairing ↔ ∃ u, exponentialCoefficient F b u < 0 := by
  have h (u : Fin m → ℝ) :
      (F.feedbackData b e).pairing ((F.feedbackData b e).orbitMatrix u *ᵥ (F.feedbackData b e).b) =
        exponentialCoefficient F b (u ∘ e.symm) := by
    rw [feedbackData_orbitMatrix]
    rfl
  unfold FeedbackData.HasNegativePairing
  simp_rw [h]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨_, hu⟩
  · rintro ⟨t, ht⟩
    refine ⟨t ∘ e, ?_⟩
    simpa [Function.comp_assoc] using ht

end LinearRepresentation

def signRationalRepresentation (p : IntegerPolynomialCode) :
    LinearRepresentation ℚ (Fin (signDimension p) → ℚ) (SignChannel p) where
  operator i := Matrix.mulVecLin ((signMatrices p i).map (Int.castRingHom ℚ))
  initial j := signInitialVector p j
  output :=
    { toFun := fun x => (signOutputRow p) ⬝ᵥ x
      map_add' := fun _ _ => dotProduct_add _ _ _
      map_smul' := fun c _ => dotProduct_smul c _ _ }

private theorem signRationalRepresentation_operator_matrix (p : IntegerPolynomialCode)
    (i : SignChannel p) :
    (signRationalRepresentation p).coordinateOperators (Pi.basisFun ℚ (Fin (signDimension p))) i =
      (signMatrices p i).map (Int.castRingHom ℚ) := by
  unfold LinearRepresentation.coordinateOperators
  rw [LinearMap.toMatrix_eq_toMatrix']
  change LinearMap.toMatrix' (Matrix.mulVecLin ((signMatrices p i).map (Int.castRingHom ℚ))) = _
  rw [← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']

private theorem signRationalRepresentation_exponentialCoefficient (p : IntegerPolynomialCode)
    (u : SignChannel p → ℝ) :
    (signRationalRepresentation p).exponentialCoefficient (Pi.basisFun ℚ (Fin (signDimension p))) u =
      p.signPolynomialValue (fun i => u (some i)) (fun i => Real.sin (u (some i))) (u none) /
        (signBaseValue p : ℝ) := by
  rw [← signPolynomial_matrix_coefficient]
  unfold LinearRepresentation.exponentialCoefficient LinearRepresentation.realOutput
    LinearRepresentation.realCoordinates realPencil
  simp_rw [signRationalRepresentation_operator_matrix]
  have hmap (i : SignChannel p) :
      (((signMatrices p i).map (Int.castRingHom ℚ)).map (Rat.castHom ℝ)) =
        (signMatrices p i).map (Int.castRingHom ℝ) := by
    ext j k
    simp
  simp_rw [hmap]
  apply Finset.sum_congr rfl
  intro j _
  have hr : (signRationalRepresentation p).output ((Pi.basisFun ℚ (Fin (signDimension p))) j) =
      signOutputRow p j := by
    simp [signRationalRepresentation, Pi.basisFun_apply]
  rw [hr]
  congr 1

/-- The rational minimal realization of the sign polynomial satisfies the feedback
hypotheses and has a negative pairing exactly for inputs with an integer root.
The choice of a rational basis here is existential. -/
theorem exists_rational_feedback (p : IntegerPolynomialCode) :
    ∃ (d m : ℕ) (K : Fin m → Matrix (Fin d) (Fin d) ℚ)
      (b ell : Fin d → ℚ),
      let F : FeedbackData d m :=
        ⟨fun i => (K i).map (Rat.castHom ℝ), fun j => (b j : ℝ), fun j => (ell j : ℝ)⟩
      F.Hypotheses ∧ (F.HasNegativePairing ↔ p.HasIntegerRoot) := by
  let F := signRationalRepresentation p
  let G := F.minimalRepresentation
  let c := Module.finBasis ℚ (F.reachable ⧸ F.unobservable)
  let e : Fin (Fintype.card (SignChannel p)) ≃ SignChannel p := (Fintype.equivFin _).symm
  have hcomm (i j : SignChannel p) : Commute (F.operator i) (F.operator j) := by
    change F.operator i * F.operator j = F.operator j * F.operator i
    apply LinearMap.ext
    intro x
    change ((signMatrices p i).map (Int.castRingHom ℚ)).mulVec
        (((signMatrices p j).map (Int.castRingHom ℚ)).mulVec x) =
      ((signMatrices p j).map (Int.castRingHom ℚ)).mulVec
        (((signMatrices p i).map (Int.castRingHom ℚ)).mulVec x)
    simp only [Matrix.mulVec_mulVec, ← Matrix.map_mul, (commute_signMatrices p i j).eq]
  have hinit : F.output F.initial = 1 := by
    have h : ((F.output F.initial : ℚ) : ℝ) = 1 := by
      change ((∑ j, signOutputRow p j * (signInitialVector p j : ℚ) : ℚ) : ℝ) = 1
      push_cast
      exact signOutput_initial p
    exact_mod_cast h
  have hinit' : G.output G.initial = 1 := by
    simpa only [LinearRepresentation.wordAction_nil, hinit] using F.minimal_output_word []
  refine ⟨_, _, fun i => G.coordinateOperators c (e i), fun j => c.repr G.initial j,
    fun j => G.output (c j), ?_⟩
  change (G.feedbackData c e).Hypotheses ∧
    ((G.feedbackData c e).HasNegativePairing ↔ p.HasIntegerRoot)
  refine ⟨G.feedbackData_hypotheses c e (fun i j => F.minimal_commute i j (hcomm i j))
    hinit' F.minimal_words_span F.minimal_rows_span, ?_⟩
  rw [LinearRepresentation.feedbackData_negative_iff]
  have hcoeff (u : SignChannel p → ℝ) : G.exponentialCoefficient c u =
      ∑ j, (signOutputRow p j : ℝ) *
        ((NormedSpace.exp (∑ i, u i • (signMatrices p i).map (Int.castRingHom ℝ))).mulVec
          (fun j => (signInitialVector p j : ℝ))) j := by
    calc
      _ = F.exponentialCoefficient (Pi.basisFun ℚ (Fin (signDimension p))) u :=
        F.minimal_exponentialCoefficient_eq _ c u
      _ = _ := (signRationalRepresentation_exponentialCoefficient p u).trans
        (signPolynomial_matrix_coefficient p u).symm
  simp_rw [hcoeff]
  exact signPolynomial_negative_matrix_coefficient_iff p

end
end PolynomialLift
end ContinuousBilinear
