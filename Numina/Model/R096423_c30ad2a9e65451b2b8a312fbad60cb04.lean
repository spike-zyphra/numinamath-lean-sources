import Mathlib

theorem algebra_257492 {x y : ℝ} (h₀ : x^3 + y^3 = 7) (h₁ : x * y * (x + y) = -2) :
    (x, y) = (2, -1) ∨ (x, y) = (-1, 2) := by
  have h2 : x + y = 1 := by
    have h3 : (x + y) ^ 3 = 1 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y - 1), sq_nonneg (x * y - (-2)), h₀, h₁]
    have h4 : (x + y) ^ 3 - 1 = 0 := by linarith
    have h5 : (x + y - 1) * ((x + y) ^ 2 + (x + y) + 1) = 0 := by
      nlinarith [h3, h4]
    cases' (mul_eq_zero.mp h5) with h7 h8
    · -- Case where \( x + y - 1 = 0 \), so \( x + y = 1 \).
      linarith [h7]
    · -- Case where \( (x+y)^2 + (x+y) + 1 = 0 \).
      have h9 : (x + y)^2 + (x + y) + 1 = 0 := by linarith [h8]
      have h10 : (x + y)^2 + (x + y) + 1 > 0 := by
        nlinarith [sq_nonneg (x + y + 1 / 2)]
      nlinarith [h9, h10]
  have h4 : x * y = -2 := by
    rw [h2] at h₁
    linarith
  have h5 : (x - 2) * (x + 1) = 0 := by
    have h6 : y = 1 - x := by linarith [h2]
    rw [h6] at h4
    nlinarith [sq_nonneg (x * (1 - x)), sq_nonneg (x - (-1)), sq_nonneg (x - 2)]
  cases' (mul_eq_zero.mp h5) with h6 h7
  · -- Case where \( x = 2 \):
    have hx : x = 2 := by linarith [h6]
    have hy : y = -1 := by linarith [show y = 1 - x by linarith [h2], hx]
    left
    exact Prod.ext hx hy
  · -- Case where \( x = -1 \):
    have hx : x = -1 := by linarith [h7]
    have hy : y = 2 := by linarith [show y = 1 - x by linarith [h2], hx]
    right
    exact Prod.ext hx hy