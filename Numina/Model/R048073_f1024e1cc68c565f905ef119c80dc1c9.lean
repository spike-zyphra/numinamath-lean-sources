import Mathlib

theorem algebra_317981 (x y : ℤ) (h : 2 * x - 3 * y = 17) :
    x ^ 2 + y ^ 2 ≥ 25 ∧ (∃ x y : ℤ, 2 * x - 3 * y = 17 ∧ x ^ 2 + y ^ 2 = 25) := by
  have h1 : x ^ 2 + y ^ 2 ≥ 25 := by
    by_contra h3
    push_neg at h3
    have h4 : x ^ 2 + y ^ 2 < 25 := h3
    have h5 : x ≤ 4 := by 
      nlinarith [sq_nonneg (x - 4 : ℤ), sq_nonneg (y + 3 : ℤ), 
        show (y + 3 : ℤ) ^ 2 ≥ 0 from sq_nonneg (y + 3 : ℤ), 
        show (x - 4 : ℤ) ^ 2 ≥ 0 from sq_nonneg (x - 4 : ℤ)
      ]
    have h6 : x ≥ -4 := by
      nlinarith [sq_nonneg (x - 4 : ℤ), sq_nonneg (y + 3 : ℤ), 
        show (y + 3 : ℤ) ^ 2 ≥ 0 from sq_nonneg (y + 3 : ℤ), 
        show (x - 4 : ℤ) ^ 2 ≥ 0 from sq_nonneg (x - 4 : ℤ)
      ]
    have h7 : y ≥ -6 := by
      nlinarith [sq_nonneg (x - 4 : ℤ), sq_nonneg (y + 3 : ℤ), 
        show (x - 4 : ℤ) ^ 2 ≥ 0 from sq_nonneg (x - 4 : ℤ), 
        show (y + 3 : ℤ) ^ 2 ≥ 0 from sq_nonneg (y + 3 : ℤ)
      ]
    have h8 : y ≤ 4 := by
      nlinarith [sq_nonneg (x - 4 : ℤ), sq_nonneg (y + 3 : ℤ), 
        show (x - 4 : ℤ) ^ 2 ≥ 0 from sq_nonneg (x - 4 : ℤ), 
        show (y + 3 : ℤ) ^ 2 ≥ 0 from sq_nonneg (y + 3 : ℤ)
      ]
    interval_cases x <;> interval_cases y <;> omega
  have h2 : ∃ x y : ℤ, 2 * x - 3 * y = 17 ∧ x ^ 2 + y ^ 2 = 25 := by
    use 4, -3
    all_goals
      norm_num
  constructor
  · exact h1
  · exact h2