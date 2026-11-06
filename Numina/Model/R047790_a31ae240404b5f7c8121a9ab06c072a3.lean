import Mathlib
open Real

theorem algebra_9284 {x : ℝ} (hx : x > 2) :
    logb 10 x + logb 10 (x - 2) = logb 10 3 + logb 10 (x + 2) ↔ x = 6 := by
  constructor
  · -- Assume $\logb 10 x + \logb 10 (x - 2) = \logb 10 3 + \logb 10 (x + 2)$, prove $x = 6$.
    intro h
    have h1 : x - 2 > 0 := by linarith
    have h2 : x + 2 > 0 := by linarith
    have h3 : logb 10 x + logb 10 (x - 2) = logb 10 (x * (x - 2)) := by
      rw [← logb_mul (by linarith) (by linarith)]
    have h4 : logb 10 3 + logb 10 (x + 2) = logb 10 (3 * (x + 2)) := by
      rw [← logb_mul (by norm_num) (by linarith)]
    rw [h3, h4] at h
    have h5 : x * (x - 2) = 3 * (x + 2) := by
      apply logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr (show x * (x - 2) > 0 by nlinarith)) (Set.mem_Ioi.mpr (show (3 * (x + 2) : ℝ) > 0 by nlinarith)) h
    -- Now $x \cdot (x - 2) = 3 \cdot (x + 2)$
    -- $x ^ 2 - 5 x - 6 = 0$.
    have h6 : x ^ 2 - 5 * x - 6 = 0 := by
      linarith [h5]
    -- Factor the quadratic
    have h7 : (x - 6) * (x + 1) = 0 := by
      nlinarith [h6]
    cases' (mul_eq_zero.mp h7) with h8 h9
    · -- x - 6 = 0
      linarith
    · -- x + 1 = 0
      nlinarith
  · -- Assume x = 6, prove $\logb 10 x + \logb 10 (x - 2) = \logb 10 3 + \logb 10 (x + 2)$.
    intro h
    rw [h]
    have h1 : (6 : ℝ) - 2 > 0 := by norm_num
    have h2 : (6 : ℝ) + 2 > 0 := by norm_num
    have h3 : logb 10 (6 : ℝ) + logb 10 (6 - 2 : ℝ) = logb 10 (6 * (6 - 2 : ℝ)) := by
      rw [← logb_mul (by norm_num) (by norm_num)]
    have h4 : logb 10 (3 : ℝ) + logb 10 (6 + 2 : ℝ) = logb 10 (3 * (6 + 2 : ℝ)) := by
      rw [← logb_mul (by norm_num) (by norm_num)]
    rw [h3, h4]
    all_goals norm_num