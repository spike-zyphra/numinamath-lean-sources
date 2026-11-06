import Mathlib
set_option maxHeartbeats 800000
theorem algebra_202712 : IsLeast {S : ℤ | ∃ a b c : ℤ, (a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ S = 3 * a ^ 2 + 2 * b ^ 2 + 4 * c ^ 2 - a * b - 3 * b * c - 5 * c * a)} 6 := by
  constructor
  · -- Show 6 is in the set.
    use 1, -1, 0 
    all_goals norm_num 
  · -- Show no smaller integer is in the set.
    intro S h 
    rcases h with ⟨a, b, c, h1, h2, h3, hS⟩
    by_contra h
    push_neg at h
    have h4 : 3 * a ^ 2 + 2 * b ^ 2 + 4 * c ^ 2 - a * b - 3 * b * c - 5 * c * a < 6 := by 
      linarith 
    have h5 : a ≤ 2 := by 
      nlinarith [sq_nonneg (a - 1 : ℤ), sq_nonneg (b + 1 : ℤ), sq_nonneg (c : ℤ), 
        sq_pos_of_ne_zero (sub_ne_zero_of_ne h1), sq_pos_of_ne_zero (sub_ne_zero_of_ne h2), sq_pos_of_ne_zero (sub_ne_zero_of_ne h3), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)
          ]
    have h6 : a ≥ -2 := by 
      nlinarith [sq_nonneg (a + 1 : ℤ), sq_nonneg (b - 1 : ℤ), sq_nonneg (c : ℤ), 
        sq_pos_of_ne_zero (sub_ne_zero_of_ne h1), sq_pos_of_ne_zero (sub_ne_zero_of_ne h2), sq_pos_of_ne_zero (sub_ne_zero_of_ne h3), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)
          ]
    have h7 : b ≤ 3 := by 
      nlinarith [sq_nonneg (a - 1 : ℤ), sq_nonneg (b - 1 : ℤ), sq_nonneg (c : ℤ), 
        sq_pos_of_ne_zero (sub_ne_zero_of_ne h1), sq_pos_of_ne_zero (sub_ne_zero_of_ne h2), sq_pos_of_ne_zero (sub_ne_zero_of_ne h3), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)
          ]
    have h8 : b ≥ -3 := by 
      nlinarith [sq_nonneg (a + 1 : ℤ), sq_nonneg (b + 1 : ℤ), sq_nonneg (c : ℤ), 
        sq_pos_of_ne_zero (sub_ne_zero_of_ne h1), sq_pos_of_ne_zero (sub_ne_zero_of_ne h2), sq_pos_of_ne_zero (sub_ne_zero_of_ne h3), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)
          ]
    have h9 : c ≤ 2 := by 
      nlinarith [sq_nonneg (a - 1 : ℤ), sq_nonneg (b : ℤ), sq_nonneg (c - 1 : ℤ), 
        sq_pos_of_ne_zero (sub_ne_zero_of_ne h1), sq_pos_of_ne_zero (sub_ne_zero_of_ne h2), sq_pos_of_ne_zero (sub_ne_zero_of_ne h3), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)
          ]
    have h10 : c ≥ -2 := by 
      nlinarith [sq_nonneg (a + 1 : ℤ), sq_nonneg (b : ℤ), sq_nonneg (c + 1 : ℤ), 
        sq_pos_of_ne_zero (sub_ne_zero_of_ne h1), sq_pos_of_ne_zero (sub_ne_zero_of_ne h2), sq_pos_of_ne_zero (sub_ne_zero_of_ne h3), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)
          ]
    interval_cases a <;> interval_cases b <;> interval_cases c <;> omega