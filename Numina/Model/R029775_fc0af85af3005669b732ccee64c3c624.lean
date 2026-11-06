import Mathlib

open Real

theorem inequalities_1865 (x : ℝ) (hx : x > 2) : (log x) ^ 2 > log (x + 1) * log (x - 1) := by
  have hx1 : x - 1 > 1 := by linarith
  have hx2 : x + 1 > 3 := by linarith
  have hx3 : log (x - 1) > 0 := by
    apply Real.log_pos
    all_goals linarith
  have hx4 : log (x + 1) > 0 := by
    apply Real.log_pos
    all_goals linarith
  have hx5 : log x > 0 := by
    apply Real.log_pos
    all_goals linarith
  have h1 : 2 * log x > log (x + 1) + log (x - 1) := by
    have h4 : log (x ^ 2) = 2 * log x := by
      simp [log_pow]
    have h5 : log ((x + 1) * (x - 1)) = log (x ^2 - 1) := by
      rw [show (x + 1) * (x - 1) = x ^2 - 1 by ring]
    have h6 : log (x ^2 - 1) < log (x ^ 2) := by
      apply Real.log_lt_log
      all_goals
        nlinarith
    have h7 : log (x + 1) + log (x - 1) = log ((x + 1) * (x - 1)) := by
      rw [log_mul (by linarith) (by linarith)]
    have h8 : log ((x + 1) * (x - 1)) = log (x ^2 - 1) := by
      rw [show (x + 1) * (x - 1) = x ^2 - 1 by ring]
    have h9 : log (x + 1) + log (x - 1) = log (x ^2 - 1) := by
      linarith [h7, h8]
    nlinarith [h4, h5, h6, h9]
  have h4 : log (x + 1) * log (x - 1) ≤ ((log (x + 1) + log (x - 1)) / 2) ^ 2 := by
    nlinarith [sq_nonneg (log (x + 1) - log (x - 1))]
  have h5 : ((log (x + 1) + log (x - 1)) / 2) ^ 2 < (log x) ^ 2 := by
    nlinarith [h1]
  nlinarith [h4, h5]