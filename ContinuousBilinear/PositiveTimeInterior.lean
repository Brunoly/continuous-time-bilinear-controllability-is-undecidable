import ContinuousBilinear.AdjointOrbitSpan
import ContinuousBilinear.EndpointInterior
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod

open Filter Topology
open scoped RightActions

attribute [local instance] LieRing.ofAssociativeRing

namespace ContinuousBilinear

section
variable {R : Type} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]
variable (S : Submonoid Rˣ)

/-- A differentiable parametrization whose values near the base point are transitions. -/
private structure EndpointChart where
  parameter : Type
  [normed : NormedAddCommGroup parameter]
  [space : NormedSpace ℝ parameter]
  [complete : CompleteSpace parameter]
  base : parameter
  endpoint : parameter → R
  derivative : parameter →L[ℝ] R
  hasDerivative : HasStrictFDerivAt endpoint derivative base
  baseUnit : Rˣ
  baseValue : endpoint base = (baseUnit : R)
  realized : ∀ᶠ x in 𝓝 base, ∃ u ∈ S, endpoint x = (u : R)

namespace EndpointChart

private noncomputable def tangent (c : EndpointChart S) : Submodule ℝ R :=
  letI := c.normed
  letI := c.space
  LinearMap.range ((LinearMap.mulRight ℝ (↑c.baseUnit⁻¹ : R)).comp c.derivative.toLinearMap)

omit [CompleteSpace R] in
private theorem mem_tangent_iff (c : EndpointChart S) (x : R) :
    x ∈ c.tangent ↔ ∃ u : c.parameter, c.derivative u * (↑c.baseUnit⁻¹ : R) = x :=
  Iff.rfl

private noncomputable def constantChart : EndpointChart S where
  parameter := ℝ
  base := 0
  endpoint := fun _ => 1
  derivative := 0
  hasDerivative := hasStrictFDerivAt_const 1 0
  baseUnit := 1
  baseValue := rfl
  realized := Filter.Eventually.of_forall fun _ => ⟨1, S.one_mem, rfl⟩

private theorem extend (c : EndpointChart S) (h : Rˣ) (hh : h ∈ S) (A : R)
    (hExp : ∀ t : ℝ, 0 < t → ∃ u ∈ S, (↑u : R) = NormedSpace.exp (t • A)) :
    ∃ d : EndpointChart S, c.tangent ≤ d.tangent ∧
      (↑c.baseUnit : R) * ↑h * A * (↑h⁻¹ * ↑c.baseUnit⁻¹) ∈ d.tangent := by
  let := c.normed
  let := c.space
  let := c.complete
  let base : c.parameter × ℝ := (c.base, 1)
  let endpoint (z : c.parameter × ℝ) := c.endpoint z.1 * ↑h * NormedSpace.exp (z.2 • A)
  obtain ⟨e, he, heval⟩ := hExp 1 zero_lt_one
  have hfst : HasStrictFDerivAt Prod.fst (ContinuousLinearMap.fst ℝ c.parameter ℝ) base :=
    hasStrictFDerivAt_fst
  have hsnd : HasStrictFDerivAt Prod.snd (ContinuousLinearMap.snd ℝ c.parameter ℝ) base :=
    hasStrictFDerivAt_snd
  have hc := c.hasDerivative.comp base hfst
  have hA := (hasStrictFDerivAt_exp_smul_const' ℝ A (1 : ℝ)).comp base hsnd
  have hd := (hc.mul_const' (↑h : R)).mul' hA
  let d : EndpointChart S :=
    { parameter := c.parameter × ℝ
      base := base
      endpoint := endpoint
      derivative := _
      hasDerivative := hd
      baseUnit := c.baseUnit * h * e
      baseValue := by simp [endpoint, base, c.baseValue, heval]
      realized := by
        have ht : Tendsto (Prod.fst : c.parameter × ℝ → c.parameter)
            (𝓝 base) (𝓝 c.base) := continuous_fst.continuousAt
        have hf : ∀ᶠ z : c.parameter × ℝ in 𝓝 base,
            ∃ u ∈ S, c.endpoint z.1 = (u : R) :=
          ht.eventually c.realized
        have hp : ∀ᶠ z : c.parameter × ℝ in 𝓝 base, 0 < z.2 :=
          continuous_snd.continuousAt (Ioi_mem_nhds zero_lt_one)
        filter_upwards [hf, hp] with z hz hzpos
        obtain ⟨u, hu, huval⟩ := hz
        obtain ⟨v, hv, hvval⟩ := hExp z.2 hzpos
        exact ⟨u * h * v, S.mul_mem (S.mul_mem hu hh) hv, by simp [endpoint, huval, hvval]⟩ }
  have hDerivative (u : c.parameter) (v : ℝ) :
      d.derivative (u, v) =
        ((↑c.baseUnit : R) * ↑h) * (v • (A * ↑e)) +
          (c.derivative u * ↑h) * ↑e := by
    simp [d, base, c.baseValue, heval, mul_assoc]
  refine ⟨d, ?_, ?_⟩
  · intro x hx
    obtain ⟨u, rfl⟩ := (EndpointChart.mem_tangent_iff S c x).mp hx
    apply (EndpointChart.mem_tangent_iff S d _).mpr
    refine ⟨(u, 0), ?_⟩
    rw [hDerivative]
    simp [d, mul_assoc]
  · apply (EndpointChart.mem_tangent_iff S d _).mpr
    refine ⟨(0, 1), ?_⟩
    rw [hDerivative]
    simp [d, mul_assoc]

end EndpointChart

/-- The positive-time transitions have interior when the available generators
span the algebra under linear combinations and brackets. -/
theorem interior_transitions_nonempty_of_lieSpan_eq_top
    [NormedAlgebra ℚ R] [FiniteDimensional ℝ R] (generators : Set R)
    (hExp : ∀ a ∈ generators, ∀ t : ℝ, 0 < t →
      ∃ u ∈ S, (↑u : R) = NormedSpace.exp (t • a))
    (hLie : LieSubalgebra.lieSpan ℝ R generators = ⊤) :
    (interior (Units.val '' (S : Set Rˣ))).Nonempty := by
  classical
  let rankRealized (k : ℕ) := ∃ c : EndpointChart S, Module.finrank ℝ c.tangent = k
  let rankBound := Module.finrank ℝ R
  have hBnd (c : EndpointChart S) : Module.finrank ℝ c.tangent ≤ rankBound :=
    Submodule.finrank_le _
  let c₀ := EndpointChart.constantChart S
  obtain ⟨c, hc⟩ := Nat.findGreatest_spec (P := rankRealized) (hBnd c₀) ⟨c₀, rfl⟩
  have hMax (d : EndpointChart S) : Module.finrank ℝ d.tangent ≤ Module.finrank ℝ c.tangent := by
    rw [hc]
    exact Nat.le_findGreatest (hBnd d) ⟨d, rfl⟩
  let C : R →ₗ[ℝ] R :=
    LinearMap.mulLeftRight ℝ (↑c.baseUnit, ↑c.baseUnit⁻¹)
  have hle : Submodule.span ℝ
      {z : R | ∃ u ∈ S, ∃ a ∈ generators, z = (↑u : R) * a * ↑u⁻¹} ≤
      c.tangent.comap C := by
    apply Submodule.span_le.mpr
    rintro _ ⟨h, hh, a, ha, rfl⟩
    obtain ⟨d, hcd, hAd⟩ := EndpointChart.extend S c h hh a (hExp a ha)
    have heq := Submodule.eq_of_le_of_finrank_le hcd (hMax d)
    rw [← heq] at hAd
    change (↑c.baseUnit : R) * (↑h * a * ↑h⁻¹) * ↑c.baseUnit⁻¹ ∈ c.tangent
    simpa only [mul_assoc] using hAd
  have hAll := span_conjugates_eq_top_of_lieSpan_eq_top S generators hExp hLie
  rw [hAll] at hle
  have hTangent (y : R) : y ∈ c.tangent := by
    have hz : (↑c.baseUnit⁻¹ : R) * y * ↑c.baseUnit ∈ c.tangent.comap C := hle trivial
    change (↑c.baseUnit : R) * (↑c.baseUnit⁻¹ * y * ↑c.baseUnit) *
      ↑c.baseUnit⁻¹ ∈ c.tangent at hz
    simpa [mul_assoc, ← mul_assoc (↑c.baseUnit : R) ↑c.baseUnit⁻¹ y] using hz
  let := c.normed
  let := c.space
  let := c.complete
  have hSurj : c.derivative.range = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨v, hv⟩ := (EndpointChart.mem_tangent_iff S c _).mp (hTangent (y * ↑c.baseUnit⁻¹))
    refine ⟨v, ?_⟩
    simpa [mul_assoc] using congrArg (fun z : R => z * (↑c.baseUnit : R)) hv
  refine ⟨c.endpoint c.base, mem_interior_of_surjective_derivative _ _ _
    c.hasDerivative hSurj ?_⟩
  filter_upwards [c.realized] with x hx
  obtain ⟨u, hu, huval⟩ := hx
  exact ⟨u, hu, huval.symm⟩

end

end ContinuousBilinear
