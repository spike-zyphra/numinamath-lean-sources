import Mathlib

theorem algebra_203797 :
    {x : ℝ | x ≥ 2 ∧ abs (1 - Real.sqrt (x - 2)) * (-x^2 + 4 * x - 3) = 1} = {2} := by

  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume x ≥ 2 ∧ abs (1 - Real.sqrt (x - 2)) * (-x^2 + 4 * x - 3) = 1, Show x = 2
    intro h
    rcases h with ⟨hx1, heq⟩
    by_cases h2 : x > 3
    · -- Assume x > 3
      -- Real.sqrt (x - 2) > 1
      have h3 : Real.sqrt (x - 2) > (1 : ℝ) := by
        have h4 : x - 2 > (1 : ℝ) := by linarith
        have h5 : Real.sqrt (x - 2) > Real.sqrt (1 : ℝ) := by
          apply Real.sqrt_lt_sqrt
          linarith
          linarith
        have h6 : Real.sqrt (1 : ℝ) = 1 := by
          norm_num [Real.sqrt_eq_iff_sq_eq]
        nlinarith
      have h4 : abs (1 - Real.sqrt (x - 2)) = Real.sqrt (x - 2) - 1 := by
        have h5 : 1 - Real.sqrt (x - 2) < 0 := by
          linarith [h3]
        rw [abs_of_neg h5]
        all_goals linarith
      rw [h4] at heq
      nlinarith [Real.sqrt_nonneg (x - 2), Real.sq_sqrt (show 0 ≤ (x - 2 : ℝ) by linarith), sq_nonneg (Real.sqrt (x - 2) - 1), sq_nonneg (x - 3), sq_nonneg ((x - 3) * (Real.sqrt (x - 2) - 1))]
    · -- Assume x ≤ 3
      have h4 : x ≤ (3 : ℝ) := by linarith
      have h5 : Real.sqrt (x - 2) ≤ (1 : ℝ) := by
        have h6 : x - 2 ≤ (1 : ℝ) := by linarith
        have h7 : Real.sqrt (x - 2) ≤ Real.sqrt (1 : ℝ) := by
          apply Real.sqrt_le_sqrt
          linarith
        have h8 : Real.sqrt (1 : ℝ) = 1 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        nlinarith
      have h7 : abs (1 - Real.sqrt (x - 2)) = 1 - Real.sqrt (x - 2) := by
        have h8 : 1 - Real.sqrt (x - 2) ≥ 0 := by
          linarith [h5]
        rw [abs_of_nonneg h8]
      rw [h7] at heq
      have h6 : Real.sqrt (x - 2) ^ 2 = x - 2 := Real.sq_sqrt (show 0 ≤ (x - 2 : ℝ) by linarith)
      nlinarith [Real.sqrt_nonneg (x - 2), sq_nonneg (Real.sqrt (x - 2) - 1), sq_nonneg (x - 3), sq_nonneg (Real.sqrt (x - 2) - 1), sq_nonneg (x - 2)]
  · -- Assume x = 2, Show x ≥ 2 ∧ abs (1 - Real.sqrt (x - 2)) * (-x^2 + 4 * x - 3) = 1
    intro heq
    rw [heq]
    constructor
    · -- Show x ≥ 2
      norm_num
    · -- Show the equation
      -- Show sqrt (0) = 0
      have h6 : Real.sqrt (2 - 2 : ℝ) = 0 := by
        rw [show (2 - 2 : ℝ) = 0 by norm_num]
        simp
      rw [h6]
      norm_num