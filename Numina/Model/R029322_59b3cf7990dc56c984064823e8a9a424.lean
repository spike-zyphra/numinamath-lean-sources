import Mathlib

open Real

theorem algebra_147904 {f : ℝ → ℝ} (hf : f = fun x => logb 2 (3 * x + 2) + 1) :
    ¬(f (1 / 3) = 0) := by
  have h1 : f (1 / 3) = logb 2 (3 * (1 / 3) + 2) + 1 := by
    rw [hf]
  have h2 : 3 * (1 / 3 : ℝ) + 2 = (3 : ℝ) := by norm_num
  rw [h2] at h1
  -- Assume f(1/3) = 0 for contradiction
  intro h
  rw [h1] at h
  -- We know that log_2(3) > 0 because 3 > 1 and base 2 > 1
  have h3 : logb (2 : ℝ) (3 : ℝ) > 0 := by
    apply logb_pos
    all_goals norm_num
  -- From h: log_2(3) + 1 = 0, which means log_2(3) = -1
  have h4 : logb (2 : ℝ) (3 : ℝ) + 1 = 0 := by linarith
  have h5 : logb (2 : ℝ) (3 : ℝ) = -1 := by linarith
  -- This contradicts h3: log_2(3) > 0
  linarith