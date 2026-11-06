import Mathlib

open Real

/-\quad \lg ^{2}(100 x)+\lg ^{2}(10 x)=14+\lg \frac{1}{x}$.-/
theorem algebra_179776 {x : ℝ} (hx : 0 < x) :
    logb 10 (100 * x) ^ 2 + logb 10 (10 * x) ^ 2 = 14 + logb 10 (1 / x) ↔
    x = 10 ^ (-9 / 2 : ℝ) ∨ x = 10 := by
  constructor
  · -- Assume the equation holds, we need to prove x = 10^(-9 / 2) or x = 10
    intro h
    have h1 : logb 10 (100 * x) = logb 10 100 + logb 10 x := by
      rw [logb_mul (by norm_num) (by linarith)]
    have h2 : logb 10 (10 * x) = logb 10 10 + logb 10 x := by
      rw [logb_mul (by norm_num) (by linarith)]
    have h3 : logb 10 (1 / x) = - logb 10 x := by
      rw [logb_div (by norm_num) (by linarith)]
      norm_num
    have h4 : logb 10 (100 : ℝ) = 2 := by
      rw [logb_eq_iff_rpow_eq] <;> norm_num
    have h5 : logb 10 (10 : ℝ) = 1 := by
      rw [logb_self_eq_one]
      all_goals norm_num
    rw [h1, h2, h3, h4, h5] at h
    have h6 : (logb 10 x) ^ 2 * 2 + (logb 10 x) * 7 - 9 = 0 := by
      nlinarith [h]
    have h7 : (logb 10 x - 1) * (2 * logb 10 x + 9) = 0 := by
      ring_nf at h6 ⊢
      linarith
    cases (mul_eq_zero.mp h7) with
    | inl h8 =>
      have hx1 : logb 10 x = 1 := by linarith
      have hx2 : x = 10 := by
        rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by linarith)] at hx1
        · linarith
      right
      exact hx2
    | inr h9 =>
      have hx1 : logb 10 x = -9 / 2 := by linarith
      have hx2 : x = 10 ^ (-9 / 2 : ℝ) := by
        rw [logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by linarith)] at hx1
        · linarith
      left
      exact hx2
  · -- Assume x = 10^(-9 / 2) or x = 10, prove the equation holds
    rintro (hx | hx)
    · -- When x = 10^(-9 / 2)
      rw [hx]
      have h1 : logb 10 (100 * (10 ^ (-9 / 2 : ℝ))) = -5 / 2 := by
        rw [logb_mul (by norm_num) (by positivity)]
        have h1a : logb 10 (100 : ℝ) = 2 := by
          rw [logb_eq_iff_rpow_eq] <;> norm_num
        have h1b : logb 10 (10 ^ (-9 / 2 : ℝ)) = -9 / 2 := by
          rw [logb_rpow (by norm_num) (by norm_num)]
        linarith [h1a, h1b]
      have h2 : logb 10 (10 * (10 ^ (-9 / 2 : ℝ))) = -7 / 2 := by
        rw [logb_mul (by norm_num) (by positivity)]
        have h2a : logb 10 (10 : ℝ) = 1 := by
          rw [logb_self_eq_one]
          all_goals norm_num
        have h2b : logb 10 (10 ^ (-9 / 2 : ℝ)) = -9 / 2 := by
          rw [logb_rpow (by norm_num) (by norm_num)]
        linarith [h2a, h2b]
      have h3 : logb 10 (1 / (10 ^ (-9 / 2 : ℝ))) = 9 / 2 := by
        have h3a : logb 10 (1 / (10 ^ (-9 / 2 : ℝ))) = - logb 10 (10 ^ (-9 / 2 : ℝ)) := by
          rw [logb_div (by norm_num) (by positivity)]
          norm_num
        have h3b : logb 10 (10 ^ (-9 / 2 : ℝ)) = -9 / 2 := by
          rw [logb_rpow (by norm_num) (by norm_num)]
        rw [h3a, h3b]
        norm_num
      rw [h1, h2, h3]
      norm_num
    · -- When x = 10
      rw [hx]
      have h1 : logb 10 (100 * (10 : ℝ)) = 3 := by
        rw [logb_mul (by norm_num) (by positivity)]
        have h1a : logb 10 (100 : ℝ) = 2 := by
          rw [logb_eq_iff_rpow_eq] <;> norm_num
        have h1b : logb 10 (10 : ℝ) = 1 := by
          rw [logb_self_eq_one]
          all_goals norm_num
        linarith [h1a, h1b]
      have h2 : logb 10 (10 * (10 : ℝ)) = 2 := by
        rw [logb_mul (by norm_num) (by positivity)]
        have h2a : logb 10 (10 : ℝ) = 1 := by
          rw [logb_self_eq_one]
          all_goals norm_num
        linarith [h2a]
      have h3 : logb 10 (1 / (10 : ℝ)) = -1 := by
        have h3a : logb 10 (1 / (10 : ℝ)) = - logb 10 (10 : ℝ) := by
          rw [logb_div (by norm_num) (by positivity)]
          norm_num
        have h3b : logb 10 (10 : ℝ) = 1 := by
          rw [logb_self_eq_one]
          all_goals norm_num
        linarith [h3a, h3b]
      rw [h1, h2, h3]
      norm_num