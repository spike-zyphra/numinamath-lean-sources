import Mathlib

theorem algebra_97107 (n : ℝ) :
    ¬(∃ x y z, n * x + y = 1 ∧ n * y + z = 1 ∧ x + n * z = 1) ↔ n = -1 := by
  constructor
  · -- Assume the system has no solution, prove n = -1
    intro h
    by_contra h1
    -- Assume n ≠ -1, we need to derive a contradiction
    have h2 : n ≠ -1 := h1
    -- We will show that if n ≠ -1, then there is a solution
    have h3 : ∃ x y z, n * x + y = 1 ∧ n * y + z = 1 ∧ x + n * z = 1 := by
      have h4 : n ^ 3 + 1 ≠ 0 := by
        by_contra h4
        have h5 : n ^ 3 = -1 := by linarith
        have h6 : n = -1 := by 
          have h7 : n ^ 3 + 1 = 0 := by linarith [h5]
          have h8 : (n + 1) * (n ^ 2 - n + 1) = 0 := by
            nlinarith 
          cases' (mul_eq_zero.1 h8) with h9 h10
          · -- n + 1 = 0, so n = -1
            linarith 
          · -- n ^ 2 - n + 1 = 0, need contradiction
            nlinarith [sq_nonneg (n - 1 / 2), sq_nonneg (n + 1), sq_nonneg (n ^ 2 - n + 1), sq_pos_of_pos (show (3 / 4 : ℝ) > 0 by norm_num)]
        -- This contradicts h2: n ≠ -1
        tauto
      -- Now construct the solution
      use (1 - n + n ^ 2) / (n ^ 3 + 1)
      use (n ^ 2 - n + 1) / (n ^ 3 + 1)
      use (n ^ 2 - n + 1) / (n ^ 3 + 1)
      constructor
      · -- Check the first equation
        field_simp [h4]
        <;> ring
      constructor
      · -- Check the second equation
        field_simp [h4]
        <;> ring
      · -- Check the third equation
        field_simp [h4]
        <;> ring
    contradiction 
  · -- Assume n = -1, prove the system has no solution
    intro h
    rw [h]
    intro h1
    rcases h1 with ⟨x, y, z, h2, h3, h4⟩
    norm_num at h2 h3 h4 
    all_goals 
      nlinarith