import Mathlib

theorem algebra_37274 {a : ℝ} (ha : a ≠ 0) (h : (a + 1 / a) ^ 2 = 11) :
    ∃ x y, x = a ^ 3 + 1 / a ^ 3 ∧ y = a ^ 5 + 1 / a ^ 5 ∧
    (x = 8 * Real.sqrt 11 ∧ y = 71 * Real.sqrt 11) ∨
    (x = -8 * Real.sqrt 11 ∧ y = -71 * Real.sqrt 11) := by
  have h1 : a ^ 2 + 1 / a ^ 2 = 9 := by
    have h2 : a ^ 2 + 1 / a ^ 2 = (a + 1 / a) ^ 2 - 2 := by
      field_simp
      nlinarith
    rw [h2, h]
    all_goals norm_num
  have h3 : (a + 1 / a) ^ 2 = 11 := h
  have h5 : (a + 1 / a) = Real.sqrt 11 ∨ (a + 1 / a) = -Real.sqrt 11 := by
    have h_eq : (a + 1 / a) ^ 2 = (Real.sqrt 11) ^ 2 := by
      rw [h3]
      rw [Real.sq_sqrt]
      all_goals norm_num
    have h6 : (a + 1 / a) = Real.sqrt 11 ∨ (a + 1 / a) = -Real.sqrt 11 := by
      apply eq_or_eq_neg_of_sq_eq_sq 
      all_goals 
        nlinarith [Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num)]
    tauto
  have h6 : a ^ 3 + 1 / a ^ 3 = (a + 1 / a) * (a ^ 2 + 1 / a ^ 2 - 1) := by 
    field_simp 
    nlinarith
  rcases h5 with h5 | h5
  · -- case $a + 1/a = \sqrt{11}$
    use 8 * Real.sqrt 11, 71 * Real.sqrt 11
    left 
    constructor
    · -- Show x = a^3 + 1/a^3
      have h7 : a ^ 3 + 1 / a ^ 3 = 8 * Real.sqrt 11 := by
        rw [h6]
        have h10 : (a + 1 / a) = Real.sqrt 11 := h5
        rw [h10, h1]
        all_goals
          nlinarith [Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num)]
      linarith
    constructor 
    · -- Show y = a^5 + 1/a^5
      have h11 : a ^ 5 + 1 / a ^ 5 = 71 * Real.sqrt 11 := by
        have h12 : a ^ 5 + 1 / a ^ 5 = (a ^ 2 + 1 / a ^ 2) * (a ^ 3 + 1 / a ^ 3) - (a + 1 / a) := by 
          field_simp 
          nlinarith [sq_nonneg (a ^ 2 - 1 / a ^ 2)]
        rw [h12, h1, show a ^ 3 + 1 / a ^ 3 = 8 * Real.sqrt 11 by
          have h7 : a ^ 3 + 1 / a ^ 3 = 8 * Real.sqrt 11 := by
            rw [h6]
            have h10 : (a + 1 / a) = Real.sqrt 11 := h5
            rw [h10, h1]
            all_goals
              nlinarith [Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num)]
          linarith 
        , h5]
        all_goals 
          nlinarith [Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num)]
      linarith 
    all_goals 
      tauto
  · -- case $a + 1/a = -\sqrt{11}$
    use -8 * Real.sqrt 11, -71 * Real.sqrt 11
    right 
    constructor 
    · -- Show x = a^3 + 1 / a^3 
      have h7 : a ^ 3 + 1 / a ^ 3 = -8 * Real.sqrt 11 := by
        rw [h6]
        have h10 : (a + 1 / a) = -Real.sqrt 11 := h5
        rw [h10, h1]
        all_goals 
          nlinarith [Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num)]
      linarith 
    · -- Show y = a^5 + 1 / a^5 
      have h11 : a ^ 5 + 1 / a ^ 5 = -71 * Real.sqrt 11 := by
        have h12 : a ^ 5 + 1 / a ^ 5 = (a ^ 2 + 1 / a ^ 2) * (a ^ 3 + 1 / a ^ 3) - (a + 1 / a) := by 
          field_simp 
          nlinarith [sq_nonneg (a ^ 2 - 1 / a ^ 2)]
        rw [h12, h1, show a ^ 3 + 1 / a ^ 3 = -8 * Real.sqrt 11 by
          have h7 : a ^ 3 + 1 / a ^ 3 = -8 * Real.sqrt 11 := by
            rw [h6]
            have h10 : (a + 1 / a) = -Real.sqrt 11 := h5
            rw [h10, h1]
            all_goals 
              nlinarith [Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num)]
          linarith 
        , h5]
        all_goals 
          nlinarith [Real.sqrt_nonneg 11, Real.sq_sqrt (show (0 : ℝ) ≤ (11 : ℝ) by norm_num)]
      linarith