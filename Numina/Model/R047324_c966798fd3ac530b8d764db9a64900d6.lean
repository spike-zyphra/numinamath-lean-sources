import Mathlib

theorem algebra_69898 {x y : ℝ} (h₀ : x + y = 3) (h₁ : x^4 - y^4 = 8 * x - y) :
    (x, y) = (2, 1) := by
  have h2 : y = 3 - x := by linarith

  rw [h2] at h₁
  have h3 : (x - 2) ^ 2 * (12 * x ^ 2 - 30 * x + 39) = 0 := by
    nlinarith [sq_nonneg (x ^ 2 - (3 - x) ^ 2), sq_nonneg ((x ^ 2 + (3 - x) ^ 2)), sq_nonneg (x - (3 - x)), sq_nonneg (x * (x - 2)), sq_nonneg ((3 - x) * (x - 2)), sq_nonneg ((x) - 2), sq_nonneg ((3 - x) - 1)]

  have h4 : (x - 2) ^ 2 = 0 ∨ (12 * x ^ 2 - 30 * x + 39) = 0 := by
    cases (mul_eq_zero.mp h3) with
    | inl h => 
      left
      nlinarith
      -- left
      -- nlinarith [sq_nonneg (12 * x ^ 2 - 30 * x + 39)]
    | inr h => 
      right
      linarith

  cases h4 with
  | inl h5 => 
    have hx1 : x = 2 := by
      nlinarith
    have hy1 : y = 1 := by
      rw [h2]
      nlinarith
    simp [hx1, hy1]
  | inr h6 => 
    have h7 : (12 * x ^ 2 - 30 * x + 39) > 0 := by
      nlinarith [sq_nonneg (x - (30 / (2 * 12))), sq_nonneg (12 * x - 15), sq_nonneg (x - 15/12), sq_nonneg (x - 2), sq_nonneg ((x) - 2), sq_nonneg ((3 - x) - 1)]
    linarith