import ContinuousBilinear.PolynomialRepresentationProof
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Quotient.Basic

namespace ContinuousBilinear
namespace PolynomialLift

/-- A state space with an initial vector, a scalar output and a family of linear operators. -/
structure LinearRepresentation (𝕜 V ι : Type*) [Field 𝕜] [AddCommGroup V] [Module 𝕜 V] where
  operator : ι → Module.End 𝕜 V
  initial : V
  output : V →ₗ[𝕜] 𝕜

namespace LinearRepresentation

variable {𝕜 V ι : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

def wordAction (F : LinearRepresentation 𝕜 V ι) : List ι → Module.End 𝕜 V
  | [] => 1
  | i :: w => F.operator i * F.wordAction w

@[simp] theorem wordAction_nil (F : LinearRepresentation 𝕜 V ι) (x : V) :
    F.wordAction [] x = x := rfl

@[simp] theorem wordAction_cons (F : LinearRepresentation 𝕜 V ι) (i : ι)
    (w : List ι) (x : V) :
    F.wordAction (i :: w) x = F.operator i (F.wordAction w x) := rfl

theorem wordAction_append (F : LinearRepresentation 𝕜 V ι) (v w : List ι) (x : V) :
    F.wordAction (v ++ w) x = F.wordAction v (F.wordAction w x) := by
  induction v with
  | nil => rfl
  | cons i v ih => simp [ih]

def reachable (F : LinearRepresentation 𝕜 V ι) : Submodule 𝕜 V :=
  Submodule.span 𝕜 (Set.range fun w => F.wordAction w F.initial)

theorem word_mem_reachable (F : LinearRepresentation 𝕜 V ι) (w : List ι) :
    F.wordAction w F.initial ∈ F.reachable := Submodule.subset_span ⟨w, rfl⟩

theorem initial_mem_reachable (F : LinearRepresentation 𝕜 V ι) :
    F.initial ∈ F.reachable := F.word_mem_reachable []

theorem operator_mem_reachable (F : LinearRepresentation 𝕜 V ι) (i : ι) (x : V)
    (hx : x ∈ F.reachable) : F.operator i x ∈ F.reachable := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl⟩ := hy
    exact F.word_mem_reachable (i :: w)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact F.reachable.add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact F.reachable.smul_mem a hx

def reachableRepresentation (F : LinearRepresentation 𝕜 V ι) :
    LinearRepresentation 𝕜 F.reachable ι where
  operator i := (F.operator i).restrict (F.operator_mem_reachable i)
  initial := ⟨F.initial, F.initial_mem_reachable⟩
  output := F.output.comp F.reachable.subtype

theorem reachable_word (F : LinearRepresentation 𝕜 V ι) (w : List ι) (x : F.reachable) :
    (F.reachableRepresentation.wordAction w x : V) = F.wordAction w (x : V) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [wordAction_cons]
    change F.operator i ((F.reachableRepresentation.wordAction w x : F.reachable) : V) = _
    rw [ih]

/-- The largest subspace of reachable vectors annihilated by all successive outputs. -/
def unobservable (F : LinearRepresentation 𝕜 V ι) : Submodule 𝕜 F.reachable :=
  ⨅ w : List ι, LinearMap.ker
    (F.reachableRepresentation.output.comp (F.reachableRepresentation.wordAction w))

theorem mem_unobservable (F : LinearRepresentation 𝕜 V ι) (x : F.reachable) :
    x ∈ F.unobservable ↔ ∀ w : List ι,
      F.reachableRepresentation.output (F.reachableRepresentation.wordAction w x) = 0 := by
  simp [unobservable]

theorem operator_mem_unobservable (F : LinearRepresentation 𝕜 V ι) (i : ι)
    (x : F.reachable) (hx : x ∈ F.unobservable) :
    F.reachableRepresentation.operator i x ∈ F.unobservable := by
  rw [mem_unobservable] at hx ⊢
  intro w
  simpa only [wordAction_append, wordAction_cons, wordAction_nil] using hx (w ++ [i])

def minimalRepresentation (F : LinearRepresentation 𝕜 V ι) :
    LinearRepresentation 𝕜 (F.reachable ⧸ F.unobservable) ι where
  operator i := F.unobservable.mapQ F.unobservable (F.reachableRepresentation.operator i)
    (F.operator_mem_unobservable i)
  initial := F.unobservable.mkQ F.reachableRepresentation.initial
  output := F.unobservable.liftQ F.reachableRepresentation.output (by
    intro x hx
    exact (F.mem_unobservable x).mp hx [])

theorem minimal_word (F : LinearRepresentation 𝕜 V ι) (w : List ι) (x : F.reachable) :
    F.minimalRepresentation.wordAction w (F.unobservable.mkQ x) =
      F.unobservable.mkQ (F.reachableRepresentation.wordAction w x) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [wordAction_cons, ih]
    rfl

theorem minimal_output_word (F : LinearRepresentation 𝕜 V ι) (w : List ι) :
    F.minimalRepresentation.output
      (F.minimalRepresentation.wordAction w F.minimalRepresentation.initial) =
      F.output (F.wordAction w F.initial) := by
  change F.minimalRepresentation.output
    (F.minimalRepresentation.wordAction w (F.unobservable.mkQ F.reachableRepresentation.initial)) = _
  rw [minimal_word]
  change F.output ((F.reachableRepresentation.wordAction w F.reachableRepresentation.initial :
    F.reachable) : V) = _
  rw [reachable_word]
  rfl

theorem minimal_commute (F : LinearRepresentation 𝕜 V ι) (i j : ι)
    (h : Commute (F.operator i) (F.operator j)) :
    Commute (F.minimalRepresentation.operator i) (F.minimalRepresentation.operator j) := by
  change F.minimalRepresentation.operator i * F.minimalRepresentation.operator j =
    F.minimalRepresentation.operator j * F.minimalRepresentation.operator i
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := F.unobservable.mkQ_surjective x
  change F.unobservable.mkQ (F.reachableRepresentation.operator i
    (F.reachableRepresentation.operator j y)) =
    F.unobservable.mkQ (F.reachableRepresentation.operator j
      (F.reachableRepresentation.operator i y))
  congr 1
  apply Subtype.ext
  exact DFunLike.congr_fun h.eq y.val

theorem minimal_word_separates (F : LinearRepresentation 𝕜 V ι)
    (x : F.reachable ⧸ F.unobservable)
    (hx : ∀ w : List ι, F.minimalRepresentation.output
      (F.minimalRepresentation.wordAction w x) = 0) : x = 0 := by
  obtain ⟨y, rfl⟩ := F.unobservable.mkQ_surjective x
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, mem_unobservable]
  intro w
  have h := hx w
  rw [minimal_word] at h
  exact h

theorem reachable_words_span (F : LinearRepresentation 𝕜 V ι) :
    F.reachableRepresentation.reachable = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  obtain ⟨y, hy⟩ := x
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl⟩ := hy
    have h := F.reachableRepresentation.word_mem_reachable w
    have he : F.reachableRepresentation.wordAction w F.reachableRepresentation.initial =
        ⟨F.wordAction w F.initial, F.word_mem_reachable w⟩ := Subtype.ext (F.reachable_word w _)
    rw [he] at h
    exact h
  | zero => exact F.reachableRepresentation.reachable.zero_mem
  | add x y hx hy hx' hy' =>
    exact F.reachableRepresentation.reachable.add_mem hx' hy'
  | smul a x hx hx' =>
    exact F.reachableRepresentation.reachable.smul_mem a hx'

theorem minimal_words_span (F : LinearRepresentation 𝕜 V ι) :
    F.minimalRepresentation.reachable = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  obtain ⟨y, rfl⟩ := F.unobservable.mkQ_surjective x
  have hy : y ∈ F.reachableRepresentation.reachable := by rw [reachable_words_span]; trivial
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl⟩ := hy
    have h := F.minimalRepresentation.word_mem_reachable w
    change F.minimalRepresentation.wordAction w
      (F.unobservable.mkQ F.reachableRepresentation.initial) ∈ _ at h
    rwa [minimal_word] at h
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact F.minimalRepresentation.reachable.add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact F.minimalRepresentation.reachable.smul_mem a hx

/-- Rows of all successive outputs are a basis-spanning family on the quotient. -/
theorem minimal_rows_span (F : LinearRepresentation 𝕜 V ι) [FiniteDimensional 𝕜 V] :
    Submodule.span 𝕜 (Set.range fun w : List ι => F.minimalRepresentation.output.comp
      (F.minimalRepresentation.wordAction w)) = ⊤ := by
  let W := Submodule.span 𝕜 (Set.range fun w : List ι => F.minimalRepresentation.output.comp
      (F.minimalRepresentation.wordAction w))
  change W = ⊤
  have hz : W.dualCoannihilator = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    rw [Submodule.mem_bot]
    apply F.minimal_word_separates x
    intro w
    exact ((Submodule.mem_dualCoannihilator x).mp hx) _
      (Submodule.subset_span ⟨w, rfl⟩)
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W), hz]
  simp

end LinearRepresentation
end PolynomialLift
end ContinuousBilinear
