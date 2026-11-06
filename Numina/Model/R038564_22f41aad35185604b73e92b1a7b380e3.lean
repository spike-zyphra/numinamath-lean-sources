import Mathlib

open Real

theorem algebra_132359 : √(√2020 - √1010) ∈ Set.Ioo 3 4 := by
  have h1 : 0 < √2020 - √1010 := by
    have h2 : √2020 > √1010 := by
      apply Real.sqrt_lt_sqrt
      all_goals norm_num
    linarith
  have h3 : 3 < √(√2020 - √1010) := by
    have h4 : 9 < √2020 - √1010 := by
      have h5 : √2020 > √1010 + 9 := by
        nlinarith [Real.sqrt_nonneg (2020 : ℝ), Real.sqrt_nonneg (1010 : ℝ), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2020 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (1010 : ℝ) by norm_num), 
          sq_nonneg (√2020 - (√1010 + 9)), 
          sq_nonneg (√1010 - (929 / 18))
        ]
      linarith
    have h7 : √(√2020 - √1010) > 3 := by
      have h8 : (√2020 - √1010) > 9 := h4
      have h9 : √(√2020 - √1010) > √(9 : ℝ) := by
        apply Real.sqrt_lt_sqrt
        all_goals nlinarith
      have h10 : √(9 : ℝ) = (3 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      linarith
    linarith
  have h4 : √(√2020 - √1010) < 4 := by
    have h10 : √2020 - √1010 < 16 := by
      have h11 : √2020 < √1010 + 16 := by
        nlinarith [Real.sqrt_nonneg (2020 : ℝ), Real.sqrt_nonneg (1010 : ℝ), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2020 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (1010 : ℝ) by norm_num), 
          sq_nonneg (√2020 - (√1010 + 16)), 
          sq_nonneg (√1010 - (754 / 32))
        ]
      linarith
    have h9 : √(√2020 - √1010) < 4 := by
      have h10 : (√2020 - √1010) < 16 := h10
      have h11 : √(√2020 - √1010) < √(16 : ℝ) := by
        apply Real.sqrt_lt_sqrt
        all_goals nlinarith
      have h12 : √16 = (4 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      linarith
    linarith
  constructor <;> (try linarith)