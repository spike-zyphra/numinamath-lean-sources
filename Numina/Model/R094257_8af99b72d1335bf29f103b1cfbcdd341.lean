import Mathlib

open Real

theorem algebra_12472 {x y z : ℝ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : log x + log z = 2 * log y) : y^2 = x * z := by
  have h1 : log x + log z = log (x * z) := by
    rw [log_mul (by linarith) (by linarith)]
  have h2 : 2 * log y = log (y ^ 2) := by
    simp [log_pow]
  rw [h1, h2] at h
  have h3 : x * z = y ^ 2 := by
    exact log_injOn_pos (by
      simp [Set.mem_setOf_eq]
      all_goals
        positivity) (by
      simp [Set.mem_setOf_eq]
      all_goals
        positivity) h
  linarith