import Mathlib

theorem inequalities_604020
    (a b c d : ℝ)
    (h₀ : 0 < a)
    (h₁ : 0 < b)
    (h₂ : 0 < c)
    (h₃ : 0 < d)
    (h₄ : a + b + c + d = 1) :
    6 * (a^3 + b^3 + c^3 + d^3) ≥ a^2 + b^2 + c^2 + d^2 + 1 / 8 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (c - d), 
          sq_nonneg (a + b + c + d - 1), sq_nonneg (a - 1 / 4), sq_nonneg (b - 1 / 4), sq_nonneg (c - 1 / 4), sq_nonneg (d - 1 / 4)
]