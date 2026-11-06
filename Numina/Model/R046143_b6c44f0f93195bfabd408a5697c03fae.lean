import Mathlib

theorem algebra_324871 (x : ℝ) (hx : 0 ≤ 5 * x ^ 2 - 1) :
    5 * x ^ 2 + x - x * Real.sqrt (5 * x ^ 2 - 1) - 2 = 0 ↔
    x = Real.sqrt 10 / 5 ∨ x = -Real.sqrt 10 / 5 := by
  constructor 
  · -- Assume the equation holds, prove the roots
    intro h_eq
    have h1 : Real.sqrt (5 * x ^ 2 - 1) ≥ 0 := by 
      apply Real.sqrt_nonneg
    by_cases h2 : x ≥ 0
    · -- Assume x ≥ 0.
      have h4 : Real.sqrt (5 * x ^ 2 - 1) ^ 2 = 5 * x ^ 2 - 1 := Real.sq_sqrt (by linarith)
      have h5 : (Real.sqrt (5 * x ^ 2 - 1) - 1) * (Real.sqrt (5 * x ^ 2 - 1) - (1 - x)) = 0 := by
        nlinarith [Real.sqrt_nonneg (5 * x ^ 2 - 1)]
      cases' (mul_eq_zero.mp h5) with h7 h8
      · -- Case sqrt(5x² - 1) = 1.
        have h7' : Real.sqrt (5 * x ^ 2 - 1) = 1 := by 
          linarith 
        have h8 : 5 * x ^ 2 - 1 = 1 := by 
          calc 
            5 * x ^ 2 - 1 = Real.sqrt (5 * x ^ 2 - 1) ^ 2 := by rw [Real.sq_sqrt]; linarith
            _ = 1 ^ 2 := by rw [h7']
            _ = (1 : ℝ) := by norm_num 
        have h9 : 5 * x ^ 2 = 2 := by linarith
        have h10 : x ^ 2 = 2 / 5 := by 
          nlinarith 
        have h11 : x = Real.sqrt 10 / 5 := by
          have h20 : x ≥ 0 := h2 
          have h13 : x ^ 2 = 2 / 5 := by 
            nlinarith 
          have h14 : x ≥ 0 := h20 
          have h15 : x = Real.sqrt (2 / 5) := by
            have h11' : x * x = 2 / 5 := by 
              nlinarith 
            have h14 : x ≥ 0 := h20 
            have h12 : x ^ 2 = 2 / 5 := by 
              nlinarith 
            have h13 : x = Real.sqrt (2 / 5) := by
              rw [← h12]
              field_simp
            linarith 
          have h17 : Real.sqrt (2 / 5) = Real.sqrt 10 / 5 := by
            have h31 : Real.sqrt (2 / 5) ^ 2 = 2 / 5 := by 
              rw [Real.sq_sqrt]
              all_goals norm_num 
            have h32 : (Real.sqrt 10 / 5) ^ 2 = 2 / 5 := by
              nlinarith [Real.sqrt_nonneg 10, Real.sq_sqrt (show 0 ≤ (10 : ℝ) by norm_num)]
            have h33 : Real.sqrt (2 / 5) ≥ 0 := by
              apply Real.sqrt_nonneg 
            have h34 : Real.sqrt 10 / 5 ≥ 0 := by 
              nlinarith [Real.sqrt_nonneg 10, Real.sq_sqrt (show 0 ≤ (10 : ℝ) by norm_num)]
            have h35 : Real.sqrt (2 / 5) = Real.sqrt 10 / 5 := by
              nlinarith [h31, h32, h33, h34]
            linarith 
          linarith
        left 
        linarith
      · -- Case sqrt(5x² - 1) = 1 - x.
        have h9 : Real.sqrt (5 * x ^ 2 - 1) = 1 - x := by
          linarith 
        have h9' : 1 - x ≥ 0 := by 
          nlinarith [Real.sqrt_nonneg (5 * x ^ 2 - 1)]
        have h10 : 5 * x ^ 2 - 1 = (1 - x) ^ 2 := by
          calc 
            5 * x ^ 2 - 1 = Real.sqrt (5 * x ^ 2 - 1) ^ 2 := by rw [Real.sq_sqrt]; linarith
            _ = (1 - x) ^ 2 := by rw [h9]
        nlinarith 
    · -- Assume x < 0.
      have h2' : x < 0 := by nlinarith 
      have h4 : Real.sqrt (5 * x ^ 2 - 1) ^ 2 = 5 * x ^ 2 - 1 := Real.sq_sqrt (by linarith)
      have h5 : (Real.sqrt (5 * x ^ 2 - 1) - 1) * (Real.sqrt (5 * x ^ 2 - 1) - (1 - x)) = 0 := by
        nlinarith [Real.sqrt_nonneg (5 * x ^ 2 - 1)]
      cases' (mul_eq_zero.mp h5) with h7 h8
      · -- Case sqrt(5x² - 1) = 1.
        have h7' : Real.sqrt (5 * x ^ 2 - 1) = 1 := by 
          linarith 
        have h8 : 5 * x ^ 2 - 1 = 1 := by 
          calc 
            5 * x ^ 2 - 1 = Real.sqrt (5 * x ^ 2 - 1) ^ 2 := by rw [Real.sq_sqrt]; linarith
            _ = 1 ^ 2 := by rw [h7']
            _ = (1 : ℝ) := by norm_num 
        have h9 : 5 * x ^ 2 = 2 := by linarith
        have h10 : x ^ 2 = 2 / 5 := by 
          nlinarith 
        have h11 : x = - Real.sqrt 10 / 5 := by
          have h11' : x ^ 2 = 2 / 5 := by 
            nlinarith 
          have h14 : x < 0 := h2' 
          have h15 : x = - Real.sqrt (2 / 5) := by 
            have h11' : x * x = 2 / 5 := by 
              nlinarith 
            have h14 : x < 0 := h2' 
            have h12 : x ^ 2 = 2 / 5 := by 
              nlinarith 
            have h13 : Real.sqrt (x ^ 2) = Real.sqrt (2 / 5) := by 
              rw [show x ^ 2 = 2 / 5 by nlinarith]
            have h14' : Real.sqrt (x^2) = -x := by 
              rw [Real.sqrt_sq_eq_abs]
              rw [abs_of_nonpos (show x ≤ 0 by linarith)]
              all_goals linarith 
            nlinarith 
          have h17 : Real.sqrt (2 / 5) = Real.sqrt 10 / 5 := by
            have h31 : Real.sqrt (2 / 5) ^ 2 = 2 / 5 := by 
              rw [Real.sq_sqrt]
              all_goals norm_num 
            have h32 : (Real.sqrt 10 / 5) ^ 2 = 2 / 5 := by
              nlinarith [Real.sqrt_nonneg 10, Real.sq_sqrt (show 0 ≤ (10 : ℝ) by norm_num)]
            have h33 : Real.sqrt (2 / 5) ≥ 0 := by
              apply Real.sqrt_nonneg 
            have h34 : Real.sqrt 10 / 5 ≥ 0 := by 
              nlinarith [Real.sqrt_nonneg 10, Real.sq_sqrt (show 0 ≤ (10 : ℝ) by norm_num)]
            have h35 : Real.sqrt (2 / 5) = Real.sqrt 10 / 5 := by
              nlinarith [h31, h32, h33, h34]
            linarith 
          linarith 
        right 
        linarith 
      · -- Case sqrt(5x² - 1) = 1 - x.
        have h9 : Real.sqrt (5 * x ^ 2 - 1) = 1 - x := by
          linarith 
        have h9' : 1 - x ≥ 0 := by 
          nlinarith [Real.sqrt_nonneg (5 * x ^ 2 - 1)]
        have h10 : 5 * x ^ 2 - 1 = (1 - x) ^ 2 := by
          calc 
            5 * x ^ 2 - 1 = Real.sqrt (5 * x ^ 2 - 1) ^ 2 := by rw [Real.sq_sqrt]; linarith
            _ = (1 - x) ^ 2 := by rw [h9]
        nlinarith
  · -- Assume the roots, prove the equation.
    rintro (h | h)
    · -- Case x = sqrt(10)/5.
      rw [h]
      have h5 : 5 * (Real.sqrt 10 / 5 : ℝ) ^ 2 - 1 = (1 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 10, Real.sq_sqrt (show 0 ≤ (10 : ℝ) by norm_num)]
      have h6 : Real.sqrt (5 * (Real.sqrt 10 / 5 : ℝ) ^ 2 - 1) = (1 : ℝ) := by
        rw [h5]
        exact Real.sqrt_one
      nlinarith [Real.sqrt_nonneg 10, Real.sq_sqrt (show 0 ≤ (10 : ℝ) by norm_num)]
    · -- Case x = -sqrt(10)/5.
      rw [h]
      have h5 : 5 * (- Real.sqrt 10 / 5 : ℝ) ^ 2 - 1 = (1 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 10, Real.sq_sqrt (show 0 ≤ (10 : ℝ) by norm_num)]
      have h6 : Real.sqrt (5 * (- Real.sqrt 10 / 5 : ℝ) ^ 2 - 1) = (1 : ℝ) := by
        rw [h5]
        exact Real.sqrt_one
      nlinarith [Real.sqrt_nonneg 10, Real.sq_sqrt (show 0 ≤ (10 : ℝ) by norm_num)]