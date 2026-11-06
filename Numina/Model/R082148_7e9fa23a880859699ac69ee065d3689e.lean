import Mathlib

theorem algebra_14441 {a b : ℝ} (ha : a > 0) (hb : b > 0)
    (hperim : 2 * (a + b) = 42) (harea : a * b = 108) :
    min a b = 9 := by
  have h1 : a + b = 21 := by
    linarith

  -- Derive the quadratic equation in terms of `a`.
  have h3 : a^2 - 21 * a + 108 = 0 := by
    have h4 : b = 21 - a := by linarith
    rw [h4] at harea
    nlinarith
  
  -- Solve the quadratic equation to get (a - 9)(a - 12) = 0
  have h4 : (a - 9) * (a - 12) = 0 := by
    nlinarith [h3]

  cases' (mul_eq_zero.1 h4) with ha1 ha2
  
  · -- Case 1: a - 9 = 0, so a = 9. Then b = 21 - a = 12
    have ha9 : a = 9 := by linarith
    have hb12 : b = 12 := by linarith [h1, ha9]
    rw [ha9, hb12]
    norm_num
  
  · -- Case 2: a - 12 = 0, so a = 12. Then b = 21 - a = 9
    have ha12 : a = 12 := by linarith
    have hb9 : b = 9 := by linarith [h1, ha12]
    rw [ha12, hb9]
    norm_num