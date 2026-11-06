import Mathlib

theorem algebra_68296 (a b : ℝ) (ha : a ≠ b) :
    ∃ x1 x2 : ℝ, x1 ≠ x2 ∧ (x1 + a) * (x1 + b) = 2 * x1 + a + b ∧
      (x2 + a) * (x2 + b) = 2 * x2 + a + b := by
  use (2 - a - b + Real.sqrt ((a - b) ^ 2 + 4)) / 2,
    (2 - a - b - Real.sqrt ((a - b) ^ 2 + 4)) / 2
  constructor
  · -- Show that $x_1 \neq x_2$ because $\sqrt{(a - b) ^ 2 + 4} \neq 0$
    by_contra h
    have h1 : Real.sqrt ((a - b) ^ 2 + 4) = 0 := by
      linarith
    have h2 : Real.sqrt ((a - b) ^ 2 + 4) > 0 := by
      apply Real.sqrt_pos.mpr
      nlinarith [sq_pos_of_ne_zero (sub_ne_zero_of_ne ha)]
    linarith
  constructor
  · -- Show that the first root satisfies the equation
    nlinarith [Real.sqrt_nonneg ((a - b) ^ 2 + 4), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (a - b) ^ 2 + 4 by
        nlinarith [sq_pos_of_ne_zero (sub_ne_zero_of_ne ha)]
      )
    ]
  · -- Show that the second root satisfies the equation
    nlinarith [Real.sqrt_nonneg ((a - b) ^ 2 + 4), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (a - b) ^ 2 + 4 by
        nlinarith [sq_pos_of_ne_zero (sub_ne_zero_of_ne ha)]
      )
    ]