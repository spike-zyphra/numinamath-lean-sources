import Mathlib

theorem algebra_9265 {x : ℕ} (h1 : x ≠ 0) (h2 : x ≠ 2) (hx : x ≤ 2) :
  ((x : ℝ) + 2 + 4 / (x - 2)) / (x ^ 3 / (x ^ 2 - 4 * x + 4)) = -1 := by
  have h3 : x = 1 := by
    interval_cases x <;> tauto
  rw [h3]
  norm_num
  <;> linarith