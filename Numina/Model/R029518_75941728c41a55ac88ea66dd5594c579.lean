import Mathlib

theorem algebra_5699
  {a b : ℝ} (h₀ : a^4 + 8 * b = 4 * (a^3 - 1) - 16 * Real.sqrt 3) (h₁ : b^4 + 8 * a = 4 * (b^3 - 1) + 16 * Real.sqrt 3) :
  a^4 + b^4 = 56 := by
  have h2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
  have h3 : Real.sqrt 3 ^ 4 = 9 := by
    calc
      Real.sqrt 3 ^ 4 = (Real.sqrt 3 ^ 2) ^ 2 := by ring
      _ = 3 ^ 2 := by rw [h2]
      _ = 9 := by norm_num

  norm_num [h2, h3] at h₀ h₁
  have h3 : (a^2 - 2*a - 2)^2 + (b^2 - 2*b - 2)^2 = 0 := by
    nlinarith [sq_nonneg (a^2 - 2*a - 2), sq_nonneg (b^2 - 2*b - 2), sq_nonneg (a - b), sq_nonneg (a + b - 2), sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (a - b), sq_nonneg (a + b - 2)]

  have h4 : a^2 - 2*a - 2 = 0 := by
    nlinarith [sq_nonneg (a^2 - 2*a - 2), sq_nonneg (b^2 - 2*b - 2), sq_nonneg (a - b), sq_nonneg (a + b - 2)]

  have h5 : b^2 - 2*b - 2 = 0 := by
    nlinarith [sq_nonneg (a^2 - 2*a - 2), sq_nonneg (b^2 - 2*b - 2), sq_nonneg (a - b), sq_nonneg (a + b - 2)]

  have h₂ : a^2 = 2*a + 2 := by linarith

  have h₃ : b^2 = 2*b + 2 := by linarith

  have h₄ : a ^ 4 = (16 * a + 12) := by
    calc
      a ^ 4 = (a^2) ^ 2 := by ring
      _ = (2*a + 2) ^ 2 := by rw [h₂]
      _ = 4*a^2 + 8*a + 4 := by ring
      _ = 4 * (2*a + 2) + 8*a + 4 := by
        rw [show a^2 = 2*a + 2 by linarith]
      _ = 8*a + 8 + 8*a + 4 := by ring
      _ = 16*a + 12 := by ring

  have h₅ : b ^ 4 = (16 * b + 12) := by
    calc
      b ^ 4 = (b^2) ^ 2 := by ring
      _ = (2*b + 2) ^ 2 := by rw [h₃]
      _ = 4*b^2 + 8*b + 4 := by ring
      _ = 4 * (2*b + 2) + 8*b + 4 := by
        rw [show b^2 = 2*b + 2 by linarith]
      _ = 8*b + 8 + 8*b + 4 := by ring
      _ = 16*b + 12 := by ring

  have h₃₅ : a + b = 2 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2)]

  linarith [h₄, h₅, h₃₅]