import Mathlib

theorem algebra_303933 {x y : ℝ} (hx : x - 5 * y + 18 * Real.sqrt (2 * y) = 20) (hy : 6 * Real.sqrt (2 * x) - x - 5 * y = 11) :
    x = 9 / 2 ∧ y = 1 / 2 := by 
  have h1 : 2 * y ≥ 0 := by
    by_contra h2
    push_neg at h2 
    have h7 : Real.sqrt (2 * y) = 0 := by 
      rw [Real.sqrt_eq_zero']
      all_goals
      nlinarith 
    rw [h7] at hx 
    by_cases h5 : 2 * x ≥ 0 
    · -- If 2*x ≥ 0.
      have h8 : (Real.sqrt (2 * x)) ^ 2 = 2 * x := by 
        have h9 : (Real.sqrt (2 * x)) ^ 2 = (2 * x) := by 
          rw [Real.sq_sqrt]
          linarith 
        linarith 
      nlinarith [Real.sqrt_nonneg (2 * x), h8, hy, h5]
    · -- 2 * x < 0 
      have h3 : 2 * x < (0 : ℝ) := by 
        by_contra h4 
        push_neg at h4 
        linarith 
      have h4 : Real.sqrt (2 * x) = 0 := by 
        rw [Real.sqrt_eq_zero']
        all_goals 
          nlinarith 
      have h5 : 6 * Real.sqrt (2 * x) = 0 := by 
        nlinarith [h4] 
      nlinarith [Real.sqrt_nonneg (2 * x), h5, hy, h3]
  have h6 : 2 * x ≥ 0 := by 
    by_contra h3 
    push_neg at h3 
    have h7 : Real.sqrt (2 * x) = 0 := by 
      rw [Real.sqrt_eq_zero']
      all_goals 
        nlinarith 
    rw [h7] at hy 
    nlinarith [Real.sqrt_nonneg (2 * y), Real.sq_sqrt (show (2 * y) ≥ 0 by linarith [h1]), sq_nonneg (Real.sqrt (2 * y) - 1)]
  -- Now that we've established the necessary non-negativity, we can try to compute values from the equations.
  have h7 : (Real.sqrt (2 * x)) ^ 2 = (2 * x) := by 
    rw [Real.sq_sqrt]
    all_goals 
      nlinarith
  have h13 : (Real.sqrt (2 * y)) ^ 2 = (2 * y) := by 
    rw [Real.sq_sqrt]
    all_goals 
      nlinarith
  have h8 : 6 * Real.sqrt (2 * x) - 2 * x - 18 * Real.sqrt (2 * y) = -9 := by 
    nlinarith 
  -- Now, prove the values of sqrt(2x) and sqrt(2y).
  -- Solving for sqrt(2x) = 3 
  have h28 : Real.sqrt (2 * x) = 3 := by
    nlinarith [ 
      sq_nonneg (Real.sqrt (2 * x) - 3), 
      sq_nonneg (Real.sqrt (2 * y) - 1), 
      Real.sqrt_nonneg (2 * x), 
      Real.sqrt_nonneg (2 * y), 
      mul_nonneg (Real.sqrt_nonneg (2 * x)) (Real.sqrt_nonneg (2 * y)), 
      h7, h13, h8, 
      sq_nonneg (x - 9 / 2), 
      sq_nonneg (y - 1 / 2)
    ]
  -- Solving for sqrt(2y) = 1 
  have h29 : Real.sqrt (2 * y) = 1 := by
    have h30 : x = 9 / 2 := by 
      have h31 : (2 * x) = 9 := by 
        have h30 : (Real.sqrt (2 * x)) ^ 2 = (2 * x) := by 
          linarith [h7]
        rw [h28] at h30 
        nlinarith 
      linarith 
    have h32 : y = 1 / 2 := by 
      nlinarith [h30, Real.sqrt_nonneg (2 * x), Real.sqrt_nonneg (2 * y), h7, h13, h8, h28]
    have h33 : (Real.sqrt (2 * y)) ^ 2 = (2 * y) := by 
      linarith [h13]
    have h34 : 2 * y = 1 := by 
      linarith [h32] 
    have h35 : (Real.sqrt (2 * y)) ^ 2 = 1 := by 
      linarith [h34, h13]
    have h36 : Real.sqrt (2 * y) ≥ 0 := by
      apply Real.sqrt_nonneg 
    have h37 : Real.sqrt (2 * y) = 1 := by 
      nlinarith 
    exact h37
  -- Solving for x and y 
  have h38 : x = 9 / 2 := by 
    have h31 : (2 * x) = 9 := by 
      have h30 : (Real.sqrt (2 * x)) ^ 2 = (2 * x) := by 
        linarith [h7]
      rw [h28] at h30 
      nlinarith 
    linarith
  have h39 : y = 1 / 2 := by 
    have h35 : 2 * y = 1 := by 
      have h30 : (Real.sqrt (2 * y)) ^ 2 = (2 * y) := by 
        linarith [h13]
      rw [h29] at h30 
      nlinarith 
    linarith 
  exact ⟨h38, h39⟩