import Mathlib

theorem algebra_101202 (x y z : ℝ) (h₀ : x ≥ y ∧ y ≥ z) (h₁ : x + y + z = 1)
    (h₂ : x ^ 2 + y ^ 2 + z ^ 2 = 3) :
    1 ≤ x ∧ x ≤ 5 / 3 := by
  have h3 : 1 ≤ x := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1), 
          h₀.1, h₀.2, 
          sq_nonneg (x - y), sq_nonneg (y - z)
         ]
  have h4 : x ≤ 5 / 3 := by
    nlinarith [sq_nonneg (x - 5 / 3), sq_nonneg (y - 5 / 3), sq_nonneg (z - 5 / 3), 
          h₀.1, h₀.2, 
          sq_nonneg (x - y), sq_nonneg (y - z)
         ]
  constructor
  · -- Proof of 1 ≤ x
    linarith
  · -- Proof of x ≤ 5/3
    linarith