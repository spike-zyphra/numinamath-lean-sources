import Mathlib

theorem algebra_2457 (x : ℝ) (hx : x ^ 2 + abs x - 6 = 0) :
    max x (-x) - min x (-x) = 4 := by 
  by_cases h : x ≥ 0
  · -- When x ≥ 0, |x| = x
    rw [abs_of_nonneg h] at hx 
    have h1 : x^2 + x - 6 = 0 := by linarith 
    have h2 : (x - 2) * (x + 3) = 0 := by
      nlinarith 
    cases' (mul_eq_zero.1 h2) with h3 h4 
    · -- Case where x - 2 = 0, so x = 2
      have hx2 : x = 2 := by linarith 
      rw [hx2]
      norm_num 
    · -- Case where x + 3 = 0, so x = -3, which contradicts x ≥ 0
      have hx3 : x = -3 := by linarith 
      linarith 
  · -- When x < 0, |x| = -x
    rw [abs_of_neg (lt_of_not_ge h)] at hx 
    have h1 : x^2 - x - 6 = 0 := by linarith 
    have h2 : (x - 3) * (x + 2) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.1 h2) with h3 h4 
    · -- Case where x - 3 = 0, so x = 3, which contradicts x < 0
      have hx3 : x = 3 := by linarith 
      linarith 
    · -- Case where x + 2 = 0, so x = -2
      have hx2 : x = -2 := by linarith 
      rw [hx2]
      norm_num