import Mathlib

theorem algebra_166224 {x y : ℝ} (h₀ : x + y + x * y = 7) (h₁ : x ^ 2 + y ^ 2 + x * y = 13) :
    (x, y) = (3, 1) ∨ (x, y) = (1, 3) := by
  have h2 : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by
    nlinarith
  have eq1 : (x + y) ^ 2 - (x * y) = 13 := by
    nlinarith [h₁, h2]
  have eq2 : x + y = 7 - (x * y) := by
    nlinarith [h₀]
  have h3 : (x * y) ^ 2 - 15 * (x * y) + 36 = 0 := by
    rw [eq2] at eq1
    nlinarith 
  have h4 : (x * y - 3) * (x * y - 12) = 0 := by
    nlinarith [h3]
  cases' (mul_eq_zero.mp h4) with h5 h6
  · -- Case where $x * y = 3$
    have hy1 : x * y = 3 := by
      linarith
    have h7 : x + y = 4 := by
      nlinarith [h₀, hy1]
    have h8 : (x - 1) * (x - 3) = 0 := by 
      nlinarith [h7, hy1]
    cases' (mul_eq_zero.mp h8) with hx1 hx2
    · -- Case where $x = 1$
      have hx : x = 1 := by linarith
      have hy : y = 3 := by linarith [h7, hx]
      right
      simp [hx, hy]
    · -- Case where $x = 3$
      have hx : x = 3 := by linarith
      have hy : y = 1 := by linarith [h7, hx]
      left
      simp [hx, hy]
  · -- Case where $x * y = 12$
    have hy2 : x * y = 12 := by
      linarith
    have h9 : x + y = -5 := by
      nlinarith [h₀, hy2]
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y + 5), sq_nonneg (x * y - 12)]