import Mathlib

open Real

theorem algebra_309243 {a b : ℝ} (ha : 1 < a) (hb : 1 < b)
    (h : log (a + b) = log a + log b) :
    log (a - 1) + log (b - 1) = 0 := by
  have h1 : a + b = a * b := by
    have pos1 : a > 0 := by linarith
    have pos2 : b > 0 := by linarith
    have pos3 : a + b > 0 := by linarith
    have h2 : log (a + b) = log (a * b) := by
      rw [h]
      have : log a + log b = log (a * b) := by
        rw [log_mul (by linarith) (by linarith)]
      linarith
      all_goals nlinarith
    have h3 : a + b = a * b := by
      apply log_injOn_pos (Set.mem_Ioi.mpr (by linarith)) (Set.mem_Ioi.mpr (by positivity)) h2
      all_goals nlinarith
    linarith
  have h2 : (a - 1) * (b - 1) = 1 := by
    nlinarith
  have h3 : log (a - 1) + log (b - 1) = log ((a - 1) * (b - 1)) := by
    rw [log_mul (by linarith) (by linarith)]
    all_goals linarith
  rw [h3]
  rw [h2]
  norm_num