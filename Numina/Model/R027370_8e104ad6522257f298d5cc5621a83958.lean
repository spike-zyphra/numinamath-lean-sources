import Mathlib

theorem algebra_8105 {x y a b : ℝ} (hx : 5 ^ x = a) (hy : 5 ^ y = b) :
    5 ^ (2 * x - y) = (a ^ 2 / b) := by
  have h1 : (5 : ℝ) ^ (2 * x - y) = (5 : ℝ) ^ (2 * x) / (5 : ℝ) ^ y := by
    rw [← Real.rpow_sub]
    ring_nf
    all_goals linarith

  have h2 : (5 : ℝ) ^ (2 * x) = ( (5 : ℝ) ^ x ) ^ 2 := by
    have h3 : (5 : ℝ) ^ (2 * x) = ((5 : ℝ) ^ x) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul]
      ring_nf
      all_goals linarith
    exact h3

  rw [h1, h2, hx, hy]
  <;> ring_nf <;> simp [Real.rpow_pos_of_pos] <;> linarith