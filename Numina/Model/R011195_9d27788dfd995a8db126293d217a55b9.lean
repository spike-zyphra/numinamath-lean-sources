import Mathlib

theorem number_theory_611248 :
    IsLeast {n : ℕ | √(n + 99) - √n < 1} 2402 := by
  constructor
  · -- Show 2402 is in the set
    have h1 : √(2402 + 99 : ℝ) - √(2402 : ℝ) < (1 : ℝ) := by
      have h4 : √(2402 + 99 : ℝ) < √(2402 : ℝ) + 1 := by
        have h5 : (√(2402 + 99 : ℝ)) ^ 2 = (2402 + 99 : ℝ) := by 
          rw [Real.sq_sqrt]
          norm_num
        have h7 : (√(2402 : ℝ) + (1 : ℝ) ) ^ 2 > (√(2402 + 99 : ℝ)) ^ 2 := by
          have h8 : (√(2402 : ℝ) + (1 : ℝ) ) ^ 2 = (√(2402 : ℝ) ^ 2 + 2 * √(2402 : ℝ) + 1 : ℝ) := by ring
          have h9 : (√(2402 + 99 : ℝ)) ^ 2 = (2402 + 99 : ℝ) := by
            rw [Real.sq_sqrt]
            norm_num
          nlinarith [Real.sqrt_nonneg (2402 : ℝ), Real.sqrt_nonneg (2402 + 99 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2402 : ℝ) by norm_num), sq_nonneg (√(2402 : ℝ) - 49), Real.sq_sqrt (show (0 : ℝ) ≤ (2402 + 99 : ℝ) by norm_num)]
        have h8 : 0 ≤ (√(2402 : ℝ) + 1 : ℝ) := by positivity
        have h9 : 0 ≤ √(2402 + 99 : ℝ) := by positivity
        nlinarith [Real.sqrt_nonneg (2402 : ℝ), Real.sqrt_nonneg (2402 + 99 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2402 : ℝ) by norm_num)]
      linarith [h4, Real.sqrt_nonneg (2402 + 99 : ℝ), Real.sqrt_nonneg (2402 : ℝ)]
    exact_mod_cast h1
  · -- Show that no smaller natural number is in the set
    intro n hn
    have h1 : √(n + 99 : ℝ) - √(n : ℝ) < (1 : ℝ) := by
      simpa using hn
    by_contra h
    push_neg at h
    have h2 : n ≤ 2401 := by omega
    have h3 : (n : ℝ) ≤ (2401 : ℝ) := by exact_mod_cast h2
    -- Show that for n ≤ 2401, the inequality is false.
    have h5 : √(n + 99 : ℝ) ≥ √(n : ℝ) + (1 : ℝ) := by
      have h6 : (n + 99 : ℝ) ≥ ((√(n : ℝ) + 1) : ℝ) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (n : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by positivity), sq_nonneg ((√(n : ℝ) - 49 : ℝ)), Real.sqrt_nonneg (n : ℝ), sq_nonneg ((n : ℝ) - (2401 : ℝ)), h3]
      have h7 : (√(n + 99 : ℝ) : ℝ) ≥ (√(n : ℝ) + (1 : ℝ) : ℝ) := by
        have h9 : (√(n + 99 : ℝ) : ℝ) ^ 2 ≥ ((√(n : ℝ) + 1) : ℝ) ^ 2 := by
          have h6' : (√(n + 99 : ℝ) : ℝ) ^ 2 = (n + 99 : ℝ) := by 
            rw [Real.sq_sqrt]
            have h44 : (n + 99 : ℝ) ≥ 0 := by positivity
            linarith
          nlinarith [h6', h6, Real.sqrt_nonneg (n : ℝ)]
        have h10 : (√(n : ℝ) + (1 : ℝ) : ℝ) ≥ 0 := by positivity
        have h11 : (√(n + 99 : ℝ) : ℝ) ≥ 0 := by positivity
        nlinarith [Real.sqrt_nonneg (n + 99 : ℝ), h9, Real.sqrt_nonneg (n : ℝ), sq_nonneg ((√(n + 99 : ℝ) : ℝ) - (√(n : ℝ) + 1 : ℝ)), Real.sq_sqrt (show (0 : ℝ) ≤ (n : ℝ) by positivity)]
      linarith
    -- Show that the original inequality is false
    have h6 : √(n + 99 : ℝ) - √(n : ℝ) ≥ (1 : ℝ) := by
      linarith [Real.sqrt_nonneg (n + 99 : ℝ), Real.sqrt_nonneg (n : ℝ), h5]
    linarith