import Mathlib

theorem algebra_222957 (x : ℝ) (hx : 0 ≤ x) :
    x + Real.sqrt (3 + Real.sqrt x) = 3 ↔ x = 1 := by
  constructor
  · -- Forward direction: if the equation holds, then x = 1
    intro h
    by_cases h2 : 3 - x ≥ 0
    · -- Assume 3 - x ≥ 0
      have h1 : Real.sqrt (3 + Real.sqrt x) = 3 - x := by linarith
      have h5 : (Real.sqrt (3 + Real.sqrt x)) ^ 2 = 3 + Real.sqrt x := by
        have h6 : 0 ≤ (3 + Real.sqrt x : ℝ) := by
          have h5 : Real.sqrt x ≥ 0 := by positivity
          linarith
        rw [Real.sq_sqrt h6]
      have h3 : (Real.sqrt (3 + Real.sqrt x)) ^ 2 = (3 - x) ^ 2 := by
        rw [h1]
        all_goals nlinarith
      -- We have 3 + Real.sqrt x = (3 - x) ^ 2
      have h6 : Real.sqrt x = x ^ 2 - 6 * x + 6 := by
        nlinarith [sq_nonneg (x - 1), sq_nonneg (x ^ 2 - 7 * x + 9), sq_nonneg (Real.sqrt x), sq_nonneg (3 - x), Real.sqrt_nonneg (3 + Real.sqrt x), Real.sqrt_nonneg x, h5, h1]
      -- Square both sides of h6 to get a polynomial equation
      have h8' : (Real.sqrt x) ^ 2 = x := by
        have h8 : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith)
        linarith
      -- Substitute h6 into h8'
      have h9' : (x ^ 2 - 6 * x + 6 : ℝ) ^ 2 = x := by
        nlinarith [h6, h8']

      -- From h9', we get a polynomial equation
      have h10 : (x - 1) * (x - 4) * (x ^ 2 - 7 * x + 9) = 0 := by
        nlinarith [sq_nonneg (x ^ 2 - 7 * x + 9), sq_nonneg (x - 4), sq_nonneg (x - 1), h6, h8']

      cases' (mul_eq_zero.mp h10) with h11 h12
      cases' (mul_eq_zero.mp h11) with h11' h12'
      · -- Case where (x - 1) = 0, so x = 1
        linarith
      · -- Case where (x - 4) = 0, so x = 4
        exfalso
        have h4 : x = 4 := by linarith
        rw [h4] at h1
        have h5 : Real.sqrt (3 + Real.sqrt (4 : ℝ)) = Real.sqrt (5 : ℝ) := by
          have h6 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by
            rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
          rw [h6]
          all_goals norm_num
          all_goals linarith
        -- Show sqrt(5) >=0 contradicting h1 which would mean sqrt(5) = -1
        have h6 : Real.sqrt (5 : ℝ) ≥ 0 := Real.sqrt_nonneg (5 : ℝ)
        nlinarith [Real.sqrt_nonneg (4 : ℝ), Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      · -- Case where x ^ 2 - 7 * x + 9 = 0
        exfalso
        nlinarith [sq_nonneg (Real.sqrt x), Real.sqrt_nonneg x, Real.sqrt_nonneg (3 + Real.sqrt x), sq_nonneg (x - 1), sq_nonneg (x ^ 2 - 7 * x + 9), Real.sq_sqrt (show (0 : ℝ) ≤ (x : ℝ) by linarith), sq_nonneg (x ^ 2 - 6 * x + 6), Real.sqrt_nonneg (3 + Real.sqrt x)]
    · -- Case where 3 - x < 0
      have h3 : Real.sqrt (3 + Real.sqrt x) ≥ 0 := by positivity
      have h4 : (3 - x : ℝ) < (0 : ℝ) := by linarith
      nlinarith [Real.sqrt_nonneg (3 + Real.sqrt x), Real.sqrt_nonneg x, Real.sq_sqrt (show (0 : ℝ) ≤ (x : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (3 + Real.sqrt x : ℝ) by
        have h5 : Real.sqrt x ≥ 0 := Real.sqrt_nonneg x
        linarith
      )
      ]
  · -- Backward direction: if x = 1, then the equation holds
    intro h
    rw [h]
    have h1 : Real.sqrt (3 + Real.sqrt (1 : ℝ)) = (2 : ℝ) := by
      rw [Real.sqrt_eq_iff_mul_self_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    nlinarith [h1, Real.sqrt_nonneg (3 + Real.sqrt (1 : ℝ)), Real.sqrt_nonneg (1 : ℝ)]