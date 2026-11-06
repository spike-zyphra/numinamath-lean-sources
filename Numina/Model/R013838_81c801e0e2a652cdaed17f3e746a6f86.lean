import Mathlib

theorem inequalities_600170 (a b : ℝ) (h : abs (a^2 - b^2) + 2 * abs (a * b) = 1) :
    Real.sqrt 2 / 2 ≤ a^2 + b^2 ∧ a^2 + b^2 ≤ 1 := by
  have h1 : a^2 + b^2 ≤ 1 := by 
    cases' abs_cases (a^2 - b^2) with h2 h2 <;> 
    cases' abs_cases (a * b) with h3 h3 <;> 
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a^2 - b^2), sq_nonneg (a * b)]
  -- Prove sqrt(2)/2 \le a^2+b^2
  have h2 : Real.sqrt 2 / 2 ≤ a^2 + b^2 := by
    have h3 : (a^2 + b^2) ^ 2 ≥ 1 / 2 := by
      cases' abs_cases (a^2 - b^2) with h4 h4 <;> 
      cases' abs_cases (a * b) with h5 h5 <;> 
      nlinarith [sq_nonneg (a^2 - b^2 - 2 * (a * b)), sq_nonneg (a^2 - b^2 + 2 * (a * b)), sq_nonneg (a^2 + b^2 - 1), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a * b), sq_nonneg (a^2 - b^2), sq_nonneg (a * b)]
    -- Show that $\sqrt{2}/2 = \sqrt{1/2}$
    have h4 : Real.sqrt 2 / 2 = Real.sqrt (1 / 2) := by
      have h5 : (Real.sqrt 2 / 2: ℝ) ^ 2 = (1 / 2 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2: ℝ) by norm_num)]
      have h6 : Real.sqrt (1 / 2 : ℝ) ^ 2 = (1 / 2 : ℝ) := by
        rw [Real.sq_sqrt]
        all_goals norm_num
      have h7 : Real.sqrt (1 / 2 : ℝ) = Real.sqrt (1 / 2 : ℝ) := by rfl
      have h8 : (0 : ℝ) ≤ Real.sqrt (1 / 2 : ℝ) := Real.sqrt_nonneg (1 / 2)
      have h9 : (0 : ℝ) ≤ (Real.sqrt 2 / 2 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2: ℝ) by norm_num)]
      -- Combine both expressions x^2 = y^2 and x, y >= 0 
      have h10 : (Real.sqrt 2 / 2: ℝ) = Real.sqrt (1 / 2 : ℝ) := by
        have h11 : (Real.sqrt 2 / 2: ℝ) ^ 2 = Real.sqrt (1 / 2 : ℝ) ^ 2 := by linarith [h5, h6]
        have h12 : Real.sqrt (1 / 2 : ℝ) ≥ 0 := Real.sqrt_nonneg (1 / 2)
        have h13 : (Real.sqrt 2 / 2: ℝ) ≥ 0 := by
          nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2: ℝ) by norm_num)]
        nlinarith [h11, h12, h13, sq_nonneg (Real.sqrt (1 / 2 : ℝ) - (Real.sqrt 2 / 2 : ℝ))]
      linarith
    rw [h4] at *
    have h5 : Real.sqrt (1 / 2) ≤ a^2 + b^2 := by
      have h8 : (a^2 + b^2) ^ 2 ≥ (1 / 2 : ℝ) := h3
      have h9 : (a^2 + b^2) ≥ Real.sqrt (1 / 2 : ℝ) := by
        have h10 : (Real.sqrt (1 / 2 : ℝ)) ^ 2 = (1 / 2 : ℝ) := by
          rw [Real.sq_sqrt]
          all_goals norm_num
        nlinarith [h8, Real.sqrt_nonneg (1 / 2 : ℝ), sq_nonneg (a^2 + b^2 - Real.sqrt (1 / 2))]
      linarith [h9]
    linarith
  constructor
  · -- Prove that Real.sqrt 2 / 2 ≤ a^2 + b^2
    linarith [h2]
  · -- Prove that a^2 + b^2 ≤ 1
    linarith [h1]