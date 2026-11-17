import Mathlib.Computability.Partrec

namespace ContinuousBilinear

/-- Computability of a finite fold with a computable step and parameter. -/
theorem computable_list_foldl {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]
    {xs : α → List β} {initial : α → σ} {step : α → σ × β → σ}
    (fallback : β) (hxs : Computable xs) (hi : Computable initial) (hstep : Computable₂ step) :
    Computable (fun a => (xs a).foldl (fun s b => step a (s, b)) (initial a)) := by
  let next (a : α) (p : ℕ × σ) := step a (p.2, (xs a).getD p.1 fallback)
  have hget : Computable (fun p : α × ℕ × σ => (xs p.1).getD p.2.1 fallback) :=
    (Primrec.option_getD.to_comp.comp
      (Computable.list_getElem?.comp (hxs.comp Computable.fst)
        (Computable.fst.comp Computable.snd)) (Computable.const fallback)).of_eq fun _ => rfl
  have hn : Computable₂ next :=
    (hstep.comp Computable.fst ((Computable.snd.comp Computable.snd).pair hget)).to₂
  have hlen : Computable (fun a => (xs a).length) := Computable.list_length.comp hxs
  refine (Computable.nat_rec hlen hi hn).of_eq fun a => ?_
  have heq (n : ℕ) (h : n ≤ (xs a).length) :
      Nat.rec (initial a) (fun k s => next a (k, s)) n =
        ((xs a).take n).foldl (fun s b => step a (s, b)) (initial a) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      have hn : n < (xs a).length := h
      rw [List.take_succ_eq_append_getElem hn, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      change next a (n, Nat.rec (initial a) (fun k s => next a (k, s)) n) = _
      rw [ih (Nat.le_of_lt hn)]
      simp only [next, List.getD_eq_getElem?_getD, getElem?_pos (xs a) n hn, Option.getD_some]
  simpa only [List.take_length] using heq (xs a).length le_rfl

/-- Computability of a finite right fold with a computable step and parameter. -/
theorem computable_list_foldr {α β σ : Type*} [Primcodable α] [Primcodable β] [Primcodable σ]
    {xs : α → List β} {initial : α → σ} {step : α → β × σ → σ}
    (fallback : β) (hxs : Computable xs) (hi : Computable initial) (hstep : Computable₂ step) :
    Computable (fun a => (xs a).foldr (fun b s => step a (b, s)) (initial a)) := by
  have hflip : Computable₂ (fun a (p : σ × β) => step a (p.2, p.1)) :=
    (hstep.comp Computable.fst
      ((Computable.snd.comp Computable.snd).pair (Computable.fst.comp Computable.snd))).to₂
  exact (computable_list_foldl fallback (Computable.list_reverse.comp hxs) hi hflip).of_eq
    (fun _ => by simp only [List.foldl_reverse])

end ContinuousBilinear
