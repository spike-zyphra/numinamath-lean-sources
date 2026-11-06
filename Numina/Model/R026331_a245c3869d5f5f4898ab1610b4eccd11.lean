import Mathlib

open Real Set

theorem algebra_223459 :
    IsLeast {x : ℝ | ∃ a b : ℝ, a ≥ 0 ∧ b ≥ 0 ∧ x = (|a - 3 * b - 2| + |3 * a - b|) / sqrt (a ^ 2 + (b + 1) ^ 2)} 2 := by
  constructor
  · -- Show 2 is in the set
    use 0, 0
    constructor
    · norm_num
    constructor
    · norm_num
    · -- Show the value of the expression is 2
      have h1 : (|0 - 3 * (0 : ℝ) - 2| + |3 * (0 : ℝ) - (0 : ℝ)| : ℝ) / sqrt ((0 : ℝ) ^ 2 + (0 + 1) ^ 2) = (2 : ℝ) := by
        have h2 : sqrt ((0 : ℝ) ^ 2 + (0 + 1) ^ 2) = 1 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [h2]
        norm_num
      linarith [h1]
  · -- Show 2 is the least element in the set
    intro x hx
    rcases hx with ⟨a, b, ha, hb, hx⟩
    have h2 : (|a - 3 * b - 2| + |3 * a - b| : ℝ) ≥ 2 * sqrt (a ^ 2 + (b + 1) ^ 2) := by
      by_cases h1 : a - 3 * b - 2 ≥ 0
      · -- Case where a - 3 * b - 2 ≥ 0
        rw [abs_of_nonneg h1]
        by_cases h2 : 3 * a - b ≥ 0
        · -- Case where 3 * a - b ≥ 0
          rw [abs_of_nonneg h2]
          nlinarith [sq_nonneg (a - 0), sq_nonneg (b - 0), 
            Real.sqrt_nonneg (a ^ 2 + (b + 1) ^ 2), 
            Real.sq_sqrt (show 0 ≤ (a ^ 2 + (b + 1) ^ 2 : ℝ) by positivity), 
            sq_nonneg (2 * a - 2 * b - 1), sq_nonneg (a - b), 
            sq_nonneg ((b - a) + 1)]
        · -- Case where 3 * a - b < 0
          rw [abs_of_neg (show (3 * a - b : ℝ) < 0 by linarith)]
          nlinarith [sq_nonneg (a - 0), sq_nonneg (b - 0), 
            Real.sqrt_nonneg (a ^ 2 + (b + 1) ^ 2), 
            Real.sq_sqrt (show 0 ≤ (a ^ 2 + (b + 1) ^ 2 : ℝ) by positivity), 
            sq_nonneg (2 * a - 2 * b - 1), sq_nonneg (a - b), 
            sq_nonneg ((b - a) + 1)]
      · -- Case where a - 3 * b - 2 < 0
        rw [abs_of_neg (show (a - 3 * b - 2 : ℝ) < 0 by linarith)]
        by_cases h2 : 3 * a - b ≥ 0
        · -- Case where 3 * a - b ≥ 0
          rw [abs_of_nonneg h2]
          nlinarith [sq_nonneg (a - 0), sq_nonneg (b - 0), 
            Real.sqrt_nonneg (a ^ 2 + (b + 1) ^ 2), 
            Real.sq_sqrt (show 0 ≤ (a ^ 2 + (b + 1) ^ 2 : ℝ) by positivity), 
            sq_nonneg (a - 0), sq_nonneg (b - 0), 
            sq_nonneg (a - b), sq_nonneg (a + b - 0)]
        · -- Case where 3 * a - b < 0
          rw [abs_of_neg (show (3 * a - b : ℝ) < 0 by linarith)]
          nlinarith [sq_nonneg (a - 0), sq_nonneg (b - 0), 
            Real.sqrt_nonneg (a ^ 2 + (b + 1) ^ 2), 
            Real.sq_sqrt (show 0 ≤ (a ^ 2 + (b + 1) ^ 2 : ℝ) by positivity), 
            sq_nonneg (a - 0), sq_nonneg (b - 0), 
            sq_nonneg (a - b), sq_nonneg (a + b - 0)]
    have h3 : (sqrt (a ^ 2 + (b + 1) ^ 2) : ℝ) > 0 := by
      have h4 : a ^ 2 + (b + 1) ^ 2 > 0 := by
        nlinarith [sq_nonneg a, sq_nonneg b, sq_pos_of_pos (show (0 : ℝ) < (0 + 1 : ℝ) by linarith)]
      positivity
    have h3' : (|a - 3 * b - 2| + |3 * a - b| : ℝ) / sqrt (a ^ 2 + (b + 1) ^ 2) ≥ (2 : ℝ) := by
      apply (le_div_iff₀ h3).mpr
      exact h2
    linarith [h3', hx]