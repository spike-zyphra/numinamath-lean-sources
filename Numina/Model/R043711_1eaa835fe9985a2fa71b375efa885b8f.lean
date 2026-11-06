import Mathlib
theorem algebra_260323 (x : ℝ) (hx : 2 * x + 1 ≥ 0 ∧ 3 * x + 5 ≥ 0) :
    3 * Real.sqrt (6 * x ^ 2 + 13 * x + 5) - 6 * Real.sqrt (2 * x + 1) - Real.sqrt (3 * x + 5) + 2 = 0 ↔
    x = -1 / 3 ∨ x = -4 / 9 := by
  constructor
  · -- Assume the equation holds, prove x = -1/3 or x = -4/9
    intro h
    rcases hx with ⟨hx1, hx2⟩
    have h1 : 6 * x ^ 2 + 13 * x + 5 = (2 * x + 1) * (3 * x + 5) := by
      nlinarith
    have h2 : Real.sqrt (6 * x ^ 2 + 13 * x + 5) = Real.sqrt (2 * x + 1) * Real.sqrt (3 * x + 5) := by
      rw [h1]
      have h2a : Real.sqrt ((2 * x + 1) * (3 * x + 5)) = Real.sqrt (2 * x + 1) * Real.sqrt (3 * x + 5) := by
        rw [Real.sqrt_mul]
        all_goals nlinarith
      exact h2a
    rw [h2] at h
    -- Solve after factorization
    have h3 : (Real.sqrt (3 * x + 5) - 2) * (3 * Real.sqrt (2 * x + 1) - 1) = 0 := by
      nlinarith [h, Real.sqrt_nonneg (2 * x + 1), Real.sqrt_nonneg (3 * x + 5), 
        Real.sq_sqrt (show 0 ≤ (2 * x + 1 : ℝ) by linarith), 
        Real.sq_sqrt (show 0 ≤ (3 * x + 5 : ℝ) by linarith)
      ]
    cases' (mul_eq_zero.1 h3) with h4 h5
    · -- Case $\sqrt{3x + 5} - 2 = 0$
      have h5 : Real.sqrt (3 * x + 5) = 2 := by linarith
      have h6 : 3 * x + 5 = 4 := by
        rw [Real.sqrt_eq_iff_sq_eq] at h5
        · linarith
        all_goals nlinarith
      have h7 : x = -1 / 3 := by linarith
      left
      exact h7
    · -- Case $3\sqrt{2x + 1} - 1 = 0$
      have h6 : 3 * Real.sqrt (2 * x + 1) - 1 = 0 := by linarith
      have h7 : Real.sqrt (2 * x + 1) = 1 / 3 := by linarith
      have h8 : 2 * x + 1 = (1 / 3 : ℝ) ^ 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] at h7
        · nlinarith
        all_goals nlinarith
      have h9 : x = -4 / 9 := by nlinarith
      right
      exact h9
  · -- Assume x = -1/3 or x = -4/9, prove the equation
    rintro (h | h)
    · -- x = -1/3
      rw [h]
      have h1 : Real.sqrt (6 * (-1/3) ^ 2 + 13 * (-1/3) + 5) = 2 / Real.sqrt (3) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf
        <;> norm_num
      have h2 : Real.sqrt (2 * (-1/3) + 1) = 1 / Real.sqrt (3) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf
        <;> norm_num
      have h3 : Real.sqrt (3 * (-1/3) + 5) = 2 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf
        <;> norm_num
      rw [h1, h2, h3]
      field_simp
      <;> ring_nf
      <;> norm_num
    · -- x = -4/9
      rw [h]
      -- Solving for x = -4/9
      -- Simplify the polynomial expressions
      have h1 : Real.sqrt (6 * (-4/9) ^ 2 + 13 * (-4/9) + 5) = Real.sqrt (2 * (-4/9) + 1) * Real.sqrt (3 * (-4/9) + 5) := by
        have h2a : Real.sqrt ((2 * (-4/9) + 1) * (3 * (-4/9) + 5)) = Real.sqrt (2 * (-4/9) + 1) * Real.sqrt (3 * (-4/9) + 5) := by
          rw [Real.sqrt_mul]
          all_goals nlinarith
        have h3a : (6 * (-4/9) ^ 2 + 13 * (-4/9) + 5 : ℝ) = (2 * (-4/9) + 1) * (3 * (-4/9) + 5) := by
          nlinarith
        have h1a : Real.sqrt (6 * (-4/9) ^ 2 + 13 * (-4/9) + 5) = Real.sqrt ((2 * (-4/9) + 1) * (3 * (-4/9) + 5)) := by
          rw [h3a]
        rw [h1a]
        exact h2a
      have h2 : Real.sqrt (2 * (-4/9) + 1) = 1 / 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf
        <;> norm_num
      have h3 : Real.sqrt (3 * (-4/9) + 5) = Real.sqrt (11 / 3 : ℝ) := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        <;> ring_nf
        <;> norm_num
      rw [h1, h2, h3]
      nlinarith [Real.sqrt_nonneg (2 * (-4/9) + 1 : ℝ), Real.sqrt_nonneg (3 * (-4/9) + 5 : ℝ), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 * (-4/9) + 1 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 * (-4/9) + 5 : ℝ) by norm_num), 
          Real.sqrt_nonneg (6 * (-4/9) ^ 2 + 13 * (-4/9) + 5 : ℝ)
      ]
  all_goals
    nlinarith
  all_goals
    nlinarith
  all_goals norm_num