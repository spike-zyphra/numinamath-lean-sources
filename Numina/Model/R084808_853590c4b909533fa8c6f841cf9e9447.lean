import Mathlib

open Real

theorem algebra_183035 {x : ℝ} (hx : 0 < x) :
    logb 10 (2 * x + 1) - logb 10 x = 2 ↔ x = 1 / 98 := by
  constructor
  · -- Assume $\lg(2x+1) - \lg(x) = 2$, prove $x = 1/98$
    intro h
    have h1 : logb 10 (2 * x + 1) = logb 10 x + 2 := by linarith
    have h2 : 2 * x + 1 > 0 := by
      nlinarith [hx]
    have eq2 : 2 * x + 1 = x * 100 := by
      have h3 : logb 10 (2 * x + 1) = logb 10 x + 2 := h1
      have h4 : logb 10 (2 * x + 1) = logb 10 (x * 100) := by
        have h5 : logb 10 (x * 100) = logb 10 x + logb 10 (100 : ℝ) := by
          rw [logb_mul (by positivity) (by positivity)]
        have h6 : logb 10 (100 : ℝ) = 2 := by
          rw [logb_eq_iff_rpow_eq] <;> (try norm_num)
        rw [h6] at h5
        linarith [h5, h3]
      have h7 : (2 * x + 1) > 0 := h2
      have h8 : (x * 100) > 0 := by nlinarith
      have h9 : (2 * x + 1) = x * 100 := by
        apply logb_injOn_pos (by norm_num) h7 h8 h4
      linarith
    nlinarith
  · -- Assume $x = 1/98$, prove $\lg(2x+1) - \lg(x) = 2$
    intro h
    rw [h]
    have h1 : (2 * (1 / 98 : ℝ) + 1) = (50 / 49 : ℝ) := by norm_num
    have h2 : (1 / 98 : ℝ) > 0 := by
      norm_num
    rw [h1]
    have h3 : logb 10 (50 / 49 : ℝ) - logb 10 (1 / 98 : ℝ) = logb 10 ((50 / 49 : ℝ) / (1 / 98 : ℝ)) := by
      rw [← logb_div (by norm_num) (by norm_num)]
    rw [h3]
    norm_num [logb_eq_iff_rpow_eq]
    <;> norm_num