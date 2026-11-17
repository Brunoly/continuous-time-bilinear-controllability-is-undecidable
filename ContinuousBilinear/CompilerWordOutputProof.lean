import ContinuousBilinear.CompilerWordBoundProof

namespace ContinuousBilinear.PolynomialLift.LinearRepresentation

variable {𝕜 V W ι : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
  [AddCommGroup W] [Module 𝕜 W]

/-- Two representations have the same word coefficients when their difference vanishes. -/
def difference (F : LinearRepresentation 𝕜 V ι) (G : LinearRepresentation 𝕜 W ι) :
    LinearRepresentation 𝕜 (V × W) ι where
  operator i := (F.operator i).prodMap (G.operator i)
  initial := (F.initial, G.initial)
  output := (F.output.comp (LinearMap.fst 𝕜 V W)) - (G.output.comp (LinearMap.snd 𝕜 V W))

@[simp] theorem difference_wordAction (F : LinearRepresentation 𝕜 V ι)
    (G : LinearRepresentation 𝕜 W ι) (w : List ι) (x : V) (y : W) :
    (F.difference G).wordAction w (x, y) = (F.wordAction w x, G.wordAction w y) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [wordAction_cons, ih]
    rfl

@[simp] theorem difference_wordOutput (F : LinearRepresentation 𝕜 V ι)
    (G : LinearRepresentation 𝕜 W ι) (w : List ι) :
    (F.difference G).output ((F.difference G).wordAction w (F.difference G).initial) =
      F.output (F.wordAction w F.initial) - G.output (G.wordAction w G.initial) := by
  change (F.difference G).output ((F.difference G).wordAction w (F.initial, G.initial)) = _
  rw [difference_wordAction]
  rfl

/-- Equality on the words up to the sum of the dimensions forces equality on every word. -/
theorem all_wordOutput_eq_of_bounded [Module.Finite 𝕜 V] [Module.Finite 𝕜 W]
    (F : LinearRepresentation 𝕜 V ι) (G : LinearRepresentation 𝕜 W ι)
    (h : ∀ w : List ι, w.length ≤ Module.finrank 𝕜 V + Module.finrank 𝕜 W →
      F.output (F.wordAction w F.initial) = G.output (G.wordAction w G.initial)) :
    ∀ w : List ι, F.output (F.wordAction w F.initial) = G.output (G.wordAction w G.initial) := by
  have hker : (F.difference G).reachable ≤ LinearMap.ker (F.difference G).output := by
    rw [(F.difference G).reachable_eq_wordSpan_finrank]
    apply Submodule.span_le.mpr
    rintro _ ⟨w, hw, rfl⟩
    rw [Module.finrank_prod] at hw
    exact (LinearMap.mem_ker.mpr (by rw [difference_wordOutput, sub_eq_zero]; exact h w hw))
  intro w
  have hm := hker ((F.difference G).word_mem_reachable w)
  simpa only [LinearMap.mem_ker, difference_wordOutput, sub_eq_zero] using hm

end ContinuousBilinear.PolynomialLift.LinearRepresentation
