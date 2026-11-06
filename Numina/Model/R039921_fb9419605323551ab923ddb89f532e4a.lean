import Mathlib

theorem algebra_248356 {a b : ℝ} (ha : a^2 * (b^2 + 1) + b * (b + 2 * a) = 40)
    (hb : a * (b + 1) + b = 8) :
    1 / a^2 + 1 / b^2 = 8 := by

  have ha1 : a ≠ 0 := by
    by_contra h
    rw [h] at hb ha
    nlinarith

  have hb1 : b ≠ 0 := by 
    by_contra h
    rw [h] at hb ha 
    nlinarith

  have eq1 : a * b + (a + b) = 8 := by 
    nlinarith

  have eq2 : (a * b)^2 + (a + b)^2 = 40 := by 
    nlinarith [sq_nonneg (a * b - 2), sq_nonneg (a + b - 6), sq_nonneg (a - b), sq_nonneg (a + b - 2)]

  have hS : (a + b) ^ 2 - 8 * (a + b) + 12 = 0 := by 
    have hP : a * b = 8 - (a + b) := by 
      nlinarith 
    rw [hP] at eq2 
    nlinarith

  have hS1 : (a + b - 6) * (a + b - 2) = 0 := by 
    nlinarith

  cases' (mul_eq_zero.mp hS1) with hS6 hS2
  · -- Case where $a + b = 6$
    have hS6' : a + b = 6 := by linarith 
    have hP : a * b = 2 := by 
      nlinarith 
    have hA2B2 : a^2 + b^2 = 32 := by 
      nlinarith 
    field_simp [(show a ≠ 0 by assumption), (show b ≠ 0 by assumption)]
    nlinarith

  · -- Case where $a + b = 2$
    have hS2' : a + b = 2 := by linarith 
    have hP : a * b = 6 := by 
      nlinarith 
    have hA2B2 : a^2 + b^2 = -8 := by 
      nlinarith

    nlinarith [sq_nonneg (a), sq_nonneg (b)]