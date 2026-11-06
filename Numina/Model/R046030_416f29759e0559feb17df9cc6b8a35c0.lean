import Mathlib
theorem algebra_308669 (a : ℝ) (h : ∃ x1 x2 : ℝ, x1 ≠ 1 ∧ x2 ≠ 1 ∧ 
(a^2 - 1) * (x1 / (x1 - 1))^2 - (2 * a + 7) * (x1 / (x1 - 1)) + 1 = 0 ∧ 
(a^2 - 1) * (x2 / (x2 - 1))^2 - (2 * a + 7) * (x2 / (x2 - 1)) + 1 = 0 ∧ (x1 / (x1 - 1)) + (x2 / (x2 - 1)) = 3 / 11) :
    a ≥ -53 / 28 := by 
  rcases h with ⟨x1, x2, hx1, hx2, h1, h2, h3⟩
  have h4 : (2 * a + 7) ^ 2 - 4 * (a ^ 2 - 1) * (1 : ℝ) ≥ 0 := by
    have h5 : (x1 / (x1 - 1) - x2 / (x2 - 1)) * ( (a ^ 2 - 1) * (x1 / (x1 - 1) + x2 / (x2 - 1)) - (2 * a + 7) ) = 0 := by
      nlinarith [sq_nonneg ((x1 / (x1 - 1)) - (x2 / (x2 - 1))), sq_nonneg ((a ^ 2 - 1) * (x1 / (x1 - 1)) - (2 * a + 7) / 2), sq_nonneg ((a ^ 2 - 1) * (x2 / (x2 - 1)) - (2 * a + 7) / 2), sq_pos_of_ne_zero (show (x1 - 1) ≠ 0 by
        intro h'
        apply hx1
        linarith
      ), sq_pos_of_ne_zero (show (x2 - 1) ≠ 0 by
        intro h'
        apply hx2
        linarith
      )
      ]
    nlinarith [sq_nonneg ((x1 / (x1 - 1)) - (x2 / (x2 - 1))), sq_nonneg ((a ^ 2 - 1) * (x1 / (x1 - 1)) - (2 * a + 7) / 2), sq_nonneg ((a ^ 2 - 1) * (x2 / (x2 - 1)) - (2 * a + 7) / 2), sq_pos_of_ne_zero (show (x1 - 1) ≠ 0 by
        intro h'
        apply hx1
        linarith
      ), sq_pos_of_ne_zero (show (x2 - 1) ≠ 0 by
        intro h'
        apply hx2
        linarith
      )
    ]
  nlinarith