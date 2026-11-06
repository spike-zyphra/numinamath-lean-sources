import Mathlib

theorem algebra_15731 (x : ℝ) (hx : 0 < x) :
    min (x ^ 2) ((4 * x) ^ 2) / max (x ^ 2) ((4 * x) ^ 2) = 1 / 16 := by
  have h1 : (4 * x) ^ 2 = 16 * x ^ 2 := by
    ring
  have h2 : min (x ^ 2) ((4 * x) ^ 2) = x ^ 2 := by
    rw [h1]
    apply min_eq_left
    nlinarith [sq_pos_of_pos hx]
  have h3 : max (x ^ 2) ((4 * x) ^ 2) = 16 * x ^ 2 := by
    rw [h1]
    apply max_eq_right
    nlinarith [sq_pos_of_pos hx]
  rw [h2, h3]
  have h4 : x ^ 2 > 0 := by
    nlinarith [sq_pos_of_pos hx]
  field_simp [h4]
  <;> ring_nf <;> nlinarith