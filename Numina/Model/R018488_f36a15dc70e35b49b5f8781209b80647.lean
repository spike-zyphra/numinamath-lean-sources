import Mathlib

theorem algebra_599400 (p q r : ℝ) (h₀ : p ≠ q) (h₁ : p ≠ r) (h₂ : q ≠ r)
    (h₃ : q = p * (4 - p)) (h₄ : r = q * (4 - q)) (h₅ : p = r * (4 - r)) :
    p + q + r = 6 ∨ p + q + r = 7 := by

  have eq2 : (p + q + r - 6) * (p + q + r - 7) = 0 := by
    nlinarith [sq_pos_of_ne_zero (show (p - q : ℝ) ≠ 0 by
      intro h
      apply h₀
      linarith
    ), sq_pos_of_ne_zero (show (p - r : ℝ) ≠ 0 by
      intro h
      apply h₁
      linarith
    ), sq_pos_of_ne_zero (show (q - r : ℝ) ≠ 0 by
      intro h
      apply h₂
      linarith
    ), sq_nonneg (p - q), sq_nonneg (q - r), sq_nonneg (r - p)]
  cases' (mul_eq_zero.mp eq2) with h6 h7
  · -- Case $p + q + r - 6 = 0$:
    left
    linarith
  · -- Case $p + q + r - 7 = 0$:
    right
    linarith