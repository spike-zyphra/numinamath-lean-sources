import Mathlib

theorem algebra_146918 (x : ℝ) (hx : x = Real.sqrt 2) :
    (x + 2)^2 - (x - 2) * (x + 2) - 4 * x^2 + 2 / x = 5 * Real.sqrt 2 := by
  rw [hx]
  have h1 : Real.sqrt 2 > 0 := by positivity
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
  have h3 : (Real.sqrt 2) ^ 4 = 4 := by
    calc
      (Real.sqrt 2) ^ 4 = ((Real.sqrt 2) ^ 2) ^ 2 := by ring
      _ = (2) ^ 2 := by rw [h2]
      _ = 4 := by norm_num
  have h4 : 2 / (Real.sqrt 2) = Real.sqrt 2 := by
    field_simp [h1]
    <;> nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  have eq1 : (Real.sqrt 2 + 2) ^ 2 = 6 + 4 * Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg 2, h2]
  have eq2 : (Real.sqrt 2 - 2) * (Real.sqrt 2 + 2) = -2 := by
    nlinarith [Real.sqrt_nonneg 2, h2]
  have eq3 : 4 * (Real.sqrt 2) ^ 2 = 8 := by
    nlinarith [h2]
  nlinarith [Real.sqrt_nonneg 2, eq1, eq2, eq3, h4]