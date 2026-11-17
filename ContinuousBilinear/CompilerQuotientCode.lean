import ContinuousBilinear.CompilerWordCoefficientProof
import ContinuousBilinear.CompilerPlantTabulationProof

namespace ContinuousBilinear.RationalFeedbackCode

open PlantCode

/-- The source code, selected prefix and suffix words, and inverse observation
matrix (stored by rows). -/
abbrev QuotientCoordinateData := RationalFeedbackCode × List (List ℕ) × List (List ℕ) × List ℚ

namespace QuotientCoordinateData

def dimension (p : QuotientCoordinateData) : ℕ := p.2.2.1.length

def inverseEntry (p : QuotientCoordinateData) (i j : ℕ) : ℚ :=
  p.2.2.2.getD (i * p.dimension + j) 0

/-- Coordinate of a word state obtained by solving the selected observation
equations with the inverse produced by elimination. -/
def wordCoordinate (p : QuotientCoordinateData) (i : ℕ) (w : List ℕ) : ℚ :=
  ((List.range p.dimension).map fun j =>
    p.inverseEntry i j * p.1.wordOutput (p.2.1.getD j [] ++ w)).sum

def operatorEntry (p : QuotientCoordinateData) (k i j : ℕ) : ℚ :=
  p.wordCoordinate i (k :: p.2.2.1.getD j [])

def quotientCode (p : QuotientCoordinateData) : RationalFeedbackCode :=
  (p.dimension, (List.range p.dimension).map (fun i => p.wordCoordinate i []),
    p.2.2.1.map p.1.wordOutput,
    (tabulatePlant p.dimension p.1.2.2.2.length (fun _ _ => 0) p.operatorEntry).2.2)

private theorem computable_getD {α β : Type*} [Primcodable α] [Primcodable β]
    {xs : α → List β} {i : α → ℕ} (hxs : Computable xs) (hi : Computable i) (d : β) :
    Computable fun a => (xs a).getD (i a) d :=
  (Primrec.option_getD.to_comp.comp (Computable.list_getElem?.comp hxs hi)
    (Computable.const d)).of_eq (fun _ => rfl)

theorem computable_dimension : Computable dimension :=
  Computable.list_length.comp (Computable.fst.comp (Computable.snd.comp Computable.snd))

theorem computable_inverseEntry :
    Computable fun q : QuotientCoordinateData × ℕ × ℕ => q.1.inverseEntry q.2.1 q.2.2 := by
  apply computable_getD (Computable.snd.comp (Computable.snd.comp
    (Computable.snd.comp Computable.fst))) _ 0
  exact Primrec.nat_add.to_comp.comp
    (Primrec.nat_mul.to_comp.comp (Computable.fst.comp Computable.snd)
      (computable_dimension.comp Computable.fst)) (Computable.snd.comp Computable.snd)

theorem computable_wordCoordinate :
    Computable fun q : QuotientCoordinateData × ℕ × List ℕ => q.1.wordCoordinate q.2.1 q.2.2 := by
  let Q := QuotientCoordinateData × ℕ × List ℕ
  apply computable_rational_sum_range (computable_dimension.comp Computable.fst)
  have hp : Computable fun r : Q × ℕ => r.1.1 := Computable.fst.comp Computable.fst
  have hi : Computable fun r : Q × ℕ => r.1.2.1 :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hw : Computable fun r : Q × ℕ => r.1.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hu : Computable fun r : Q × ℕ => r.1.1.2.1.getD r.2 [] :=
    computable_getD (Computable.fst.comp (Computable.snd.comp hp)) Computable.snd []
  have hMoment : Computable fun r : Q × ℕ =>
      r.1.1.1.wordOutput (r.1.1.2.1.getD r.2 [] ++ r.1.2.2) :=
    computable_wordOutput.comp (Computable.fst.comp hp) (Primrec.list_append.to_comp.comp hu hw)
  exact (computable_rat_mul.comp
    (computable_inverseEntry.comp (hp.pair (hi.pair Computable.snd))) hMoment).to₂

set_option maxHeartbeats 600000 in
theorem computable_operatorEntry :
    Computable fun q : (QuotientCoordinateData × ℕ) × ℕ × ℕ =>
      q.1.1.operatorEntry q.1.2 q.2.1 q.2.2 := by
  let Q := (QuotientCoordinateData × ℕ) × ℕ × ℕ
  have hp : Computable fun r : Q => r.1.1 := Computable.fst.comp Computable.fst
  have hj : Computable fun r : Q => r.2.2 := Computable.snd.comp Computable.snd
  have hv : Computable fun r : Q => r.1.1.2.2.1.getD r.2.2 [] :=
    computable_getD (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hp))) hj []
  have hk : Computable fun r : Q => r.1.2 := Computable.snd.comp Computable.fst
  have hi : Computable fun r : Q => r.2.1 := Computable.fst.comp Computable.snd
  have hword : Computable fun r : Q => r.1.2 :: r.1.1.2.2.1.getD r.2.2 [] :=
    Primrec.list_cons.to_comp.comp hk hv
  have hargs : Computable fun r : Q => (r.1.1, r.2.1, r.1.2 :: r.1.1.2.2.1.getD r.2.2 []) :=
    hp.pair (hi.pair hword)
  exact (computable_wordCoordinate.comp hargs).of_eq fun _ => rfl

theorem computable_quotientCode : Computable quotientCode := by
  have hi : Computable fun p : QuotientCoordinateData =>
      (List.range p.dimension).map (fun i => p.wordCoordinate i []) :=
    computable_list_map (Primrec.list_range.to_comp.comp computable_dimension)
      (computable_wordCoordinate.comp (Computable.fst.pair
        (Computable.snd.pair (Computable.const ([] : List ℕ))))).to₂
  have ho : Computable fun p : QuotientCoordinateData => p.2.2.1.map p.1.wordOutput :=
    computable_list_map (Computable.fst.comp (Computable.snd.comp Computable.snd))
      (computable_wordOutput.comp (Computable.fst.comp Computable.fst) Computable.snd).to₂
  have hm : Computable fun p : QuotientCoordinateData => p.1.2.2.2.length :=
    Computable.list_length.comp (Computable.snd.comp (Computable.snd.comp
      (Computable.snd.comp Computable.fst)))
  have htab := computable_tabulatePlant computable_dimension hm
    (Computable.const (0 : ℚ)) computable_operatorEntry
  exact computable_dimension.pair (hi.pair (ho.pair
    ((Computable.snd.comp Computable.snd).comp htab)))

end QuotientCoordinateData
end ContinuousBilinear.RationalFeedbackCode
