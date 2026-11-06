import Mathlib

theorem algebra_108831 {a b : ℝ × ℝ}
    (h₀ : Real.sqrt ((a.1 - b.1)^2 + (a.2 - b.2)^2) = 3)
    (h₁ : Real.sqrt ((a.1 + 2 * b.1)^2 + (a.2 + 2 * b.2)^2) = 6)
    (h₂ : a.1^2 + a.1 * b.1 - 2 * b.1^2 + a.2^2 + a.2 * b.2 - 2 * b.2^2 = -9) :
    Real.sqrt (b.1^2 + b.2^2) = Real.sqrt 7 := by
  have h0' : (a.1 - b.1)^2 + (a.2 - b.2)^2 = 9 := by
    calc
      (a.1 - b.1)^2 + (a.2 - b.2)^2 = (Real.sqrt ((a.1 - b.1)^2 + (a.2 - b.2)^2))^2 := by rw [Real.sq_sqrt]; positivity
      _ = 3^2 := by rw [h₀]
      _ = 9 := by norm_num
  have h1' : (a.1 + 2 * b.1)^2 + (a.2 + 2 * b.2)^2 = 36 := by
    calc
      (a.1 + 2 * b.1)^2 + (a.2 + 2 * b.2)^2 = (Real.sqrt ((a.1 + 2 * b.1)^2 + (a.2 + 2 * b.2)^2))^2 := by rw [Real.sq_sqrt]; positivity
      _ = 6^2 := by rw [h₁]
      _ = 36 := by norm_num
  have eq1 : a.1^2 + a.2^2 - 2 * (a.1 * b.1 + a.2 * b.2) + (b.1^2 + b.2^2) = 9 := by
    nlinarith [h0']
  have eq2 : a.1^2 + a.2^2 + 4 * (a.1 * b.1 + a.2 * b.2) + 4 * (b.1^2 + b.2^2) = 36 := by
    nlinarith [h1']
  have eq3 : a.1^2 + a.2^2 + (a.1 * b.1 + a.2 * b.2) - 2 * (b.1^2 + b.2^2) = -9 := by
    linarith [h₂]
  have h3 : a.1^2 + a.2^2 = (b.1^2 + b.2^2) - 3 := by
    nlinarith [eq1, eq3]
  have h4 : 9 * (b.1^2 + b.2^2) = 63 := by
    nlinarith [eq2, h3]
  have h5 : b.1^2 + b.2^2 = 7 := by
    nlinarith
  rw [h5]