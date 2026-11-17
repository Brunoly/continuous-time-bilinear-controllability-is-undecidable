import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Tactic.NoncommRing

namespace ContinuousBilinear

section Ring

variable {R : Type*} [Ring R] {u v : R}

/-- Algebraic form of the order-four rotation obtained by composing two shears
whose pairing is minus one. -/
theorem shearProduct_pow_four (hu : u * u = 0) (hv : v * v = 0)
    (huv : u * v * u = -u) (hvu : v * u * v = -v) :
    ((1 + u) * (1 + v) * (1 + u)) ^ 4 = 1 := by
  let e := -(u * v + v * u)
  let s := u + v
  have heu : e * u = u := by
    simp [e, add_mul, huv, mul_assoc v u u, hu]
  have hev : e * v = v := by
    simp [e, add_mul, hvu, mul_assoc u v v, hv]
  have hue : u * e = u := by
    simp [e, mul_add, ← mul_assoc u, hu, huv]
  have hve : v * e = v := by
    simp [e, mul_add, ← mul_assoc v, hv, hvu]
  have he : e * e = e := by
    conv_lhs => congr; rfl; rw [show e = -(u * v + v * u) from rfl]
    rw [mul_neg, mul_add, ← mul_assoc, ← mul_assoc, heu, hev]
  have hes : e * s = s := by simp [s, mul_add, heu, hev]
  have hse : s * e = s := by simp [s, add_mul, hue, hve]
  have hs : s * s = -e := by
    simp [s, e, add_mul, mul_add, hu, hv, add_comm]
  have hP : (1 + u) * (1 + v) * (1 + u) = 1 - e + s := by
    calc
      _ = 1 + u + v + u * v + u + u * u + v * u + u * v * u := by noncomm_ring
      _ = _ := by rw [hu, huv]; dsimp [e, s]; abel
  have hP2 : (1 - e + s) ^ 2 = 1 - 2 * e := by
    calc
      _ = 1 - 2 * e + e * e + 2 * s - e * s - s * e + s * s := by noncomm_ring
      _ = _ := by rw [he, hes, hse, hs]; noncomm_ring
  rw [hP, show 4 = 2 * 2 by rfl, pow_mul, hP2]
  rw [show (2 : R) * e = e + e by noncomm_ring, pow_two]
  simp only [sub_mul, mul_sub, add_mul, mul_add, one_mul, mul_one, he]
  abel

/-- The two inverse shears belong to any submonoid that contains the corresponding
positive shears at a parameter product with pairing minus one. -/
theorem submonoid_mem_inverse_shears (S : Submonoid R)
    (hT : 1 + u ∈ S) (hL : 1 + v ∈ S)
    (hu : u * u = 0) (hv : v * v = 0)
    (huv : u * v * u = -u) (hvu : v * u * v = -v) :
    1 - u ∈ S ∧ 1 - v ∈ S := by
  let T := 1 + u
  let L := 1 + v
  let P := T * L * T
  have hTu : T * (1 - u) = 1 := by
    dsimp [T]; rw [show (1 + u) * (1 - u) = 1 - u * u by noncomm_ring, hu, sub_zero]
  have huT : (1 - u) * T = 1 := by
    dsimp [T]; rw [show (1 - u) * (1 + u) = 1 - u * u by noncomm_ring, hu, sub_zero]
  have hLv : L * (1 - v) = 1 := by
    dsimp [L]; rw [show (1 + v) * (1 - v) = 1 - v * v by noncomm_ring, hv, sub_zero]
  have hP : P ^ 4 = 1 := shearProduct_pow_four hu hv huv hvu
  have hmem : P ^ 3 ∈ S := S.pow_mem (S.mul_mem (S.mul_mem hT hL) hT) _
  have hPinv : P ^ 3 = (1 - u) * (1 - v) * (1 - u) := by
    have hcancel : P * ((1 - u) * (1 - v) * (1 - u)) = 1 := by
      calc
        _ = T * (L * ((T * (1 - u)) * (1 - v))) * (1 - u) := by dsimp [P]; noncomm_ring
        _ = 1 := by rw [hTu, one_mul, hLv, mul_one, hTu]
    calc
      _ = P ^ 3 * (P * ((1 - u) * (1 - v) * (1 - u))) := by rw [hcancel, mul_one]
      _ = _ := by rw [← mul_assoc, ← pow_succ, hP, one_mul]
  have h1 : L * T * P ^ 3 = 1 - u := by
    rw [hPinv]
    calc
      _ = L * (T * (1 - u)) * (1 - v) * (1 - u) := by noncomm_ring
      _ = _ := by rw [hTu, mul_one, hLv, one_mul]
  have h2 : T * P ^ 3 * T = 1 - v := by
    rw [hPinv]
    calc
      _ = (T * (1 - u)) * (1 - v) * ((1 - u) * T) := by noncomm_ring
      _ = _ := by rw [hTu, huT, one_mul, mul_one]
  exact ⟨h1 ▸ S.mul_mem (S.mul_mem hL hT) hmem,
    h2 ▸ S.mul_mem (S.mul_mem hT hmem) hT⟩

end Ring
end ContinuousBilinear
