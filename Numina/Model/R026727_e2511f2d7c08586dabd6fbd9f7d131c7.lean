import Mathlib

open Real

theorem algebra_14033 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : log (2^x) + log (8^y) = log 4) :
    8 ≤ 1 / x + 3 / y := by

  have h1 : log (2 ^ x) = x * log 2 := by
    rw [log_rpow]
    all_goals linarith
  have h2 : log (8 ^ y) = y * log 8 := by
    rw [log_rpow]
    all_goals linarith

  have h3 : log 8 = 3 * log 2 := by
    rw [show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num]
    simp [log_pow]

  have h4 : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num]
    simp [log_pow]

  have h5 : log (2 ^ x) + log (8 ^ y) = x * log 2 + y * (3 * log 2) := by 
    rw [h1, h2, h3]
    all_goals ring

  have h6 : x * log 2 + y * (3 * log 2) = 2 * log 2 := by 
    linarith [h, h5, h4]

  have h7 : x + 3 * y = 2 := by
    have h2_ne_zero : log 2 ≠ 0 := by 
      positivity 
    have eq1 : (x + 3 * y) * log 2 = 2 * log 2 := by 
      linarith [h6]
    have eq2 : x + 3 * y = 2 := by 
      apply (mul_left_inj' h2_ne_zero).mp 
      linarith 
    linarith

  have h8 : 0 < x := hx
  have h9 : 0 < y := hy

  have h10 : 1 / x + 3 / y - 8 ≥ 0 := by
    have h11 : x * y > 0 := mul_pos hx hy
    have h12 : y + 3 * x ≥ 8 * x * y := by 
      nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (y - 1 / 2), 
          h7, mul_pos hx hy, 
          mul_pos (show 0 < 2 - x by nlinarith [h7, hx]) 
            (show 0 < 2 - x by nlinarith [h7, hx]), 
          mul_pos hy (show 0 < 2 - x by nlinarith [h7, hx])]
    
    have h13 : (1 / x + 3 / y - 8) = (y + 3 * x - 8 * x * y) / (x * y) := by 
      field_simp 
      <;> ring

    rw [h13]

    apply div_nonneg 
    linarith [h12]
    positivity

  linarith [h10]