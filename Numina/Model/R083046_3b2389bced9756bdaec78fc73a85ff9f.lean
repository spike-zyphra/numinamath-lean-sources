import Mathlib

theorem algebra_224139 :
    ∃ a b : ℕ, Real.sqrt (3 + 2 * Real.sqrt 2) = Real.sqrt a + Real.sqrt b ∧
    ∃ a b : ℕ, Real.sqrt (9 + 4 * Real.sqrt 5) = Real.sqrt a + Real.sqrt b ∧
    ∃ a b : ℕ, Real.sqrt (7 - 2 * Real.sqrt 10) = Real.sqrt a - Real.sqrt b := by

  use 1, 2
  constructor
  · -- Show that sqrt(3 + 2 * sqrt 2) = sqrt 1 + sqrt 2
    have h1 : Real.sqrt (3 + 2 * Real.sqrt 2) = 1 + Real.sqrt 2 := by
      have h2 : (1 + Real.sqrt 2) ^ 2 = 3 + 2 * Real.sqrt 2 := by
        ring_nf
        rw [Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        all_goals linarith [Real.sqrt_nonneg 2]
      have h5 : 0 ≤ (1 + Real.sqrt 2 : ℝ) := by
        nlinarith [Real.sqrt_nonneg 2]
      rw [← h2]
      field_simp [Real.sqrt_sq h5]
    rw [h1]
    simp
  · -- Part b)
    use 4, 5
    constructor
    · -- Show that sqrt(9 + 4 * sqrt 5) = sqrt 4 + sqrt 5
      have h1 : Real.sqrt (9 + 4 * Real.sqrt 5) = 2 + Real.sqrt 5 := by
        have h2 : (2 + Real.sqrt 5) ^ 2 = 9 + 4 * Real.sqrt 5 := by
          ring_nf
          rw [Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
          all_goals linarith [Real.sqrt_nonneg 5]
        have h5 : 0 ≤ (2 + Real.sqrt 5 : ℝ) := by
          nlinarith [Real.sqrt_nonneg 5]
        rw [← h2]
        field_simp [Real.sqrt_sq h5]
      rw [h1]
      have h5 : Real.sqrt (4 : ℝ) = (2 : ℝ) := Real.sqrt_eq_cases.2 (by norm_num)
      simp [h5]
    · -- Part c)
      use 5, 2
      -- Show that sqrt(7 - 2 * sqrt 10) = sqrt 5 - sqrt 2
      have h1 : Real.sqrt (7 - 2 * Real.sqrt 10) = Real.sqrt 5 - Real.sqrt 2 := by
        have h2 : (Real.sqrt 5 - Real.sqrt 2) ^ 2 = 7 - 2 * Real.sqrt 10 := by
          have h3 : (Real.sqrt 5) ^ 2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
          have h4 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
          have h5 : Real.sqrt 10 = Real.sqrt 5 * Real.sqrt 2 := by
            rw [← Real.sqrt_mul (by norm_num)]
            norm_num
          nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 2, h3, h4, h5]
        have h6 : 0 ≤ (Real.sqrt 5 - Real.sqrt 2 : ℝ) := by
          have h7 : Real.sqrt 2 ≤ Real.sqrt 5 := Real.sqrt_le_sqrt (by norm_num)
          have h8 : Real.sqrt 2 ≤ (2 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
          have h9 : Real.sqrt 5 ≥ (2 : ℝ) := by
            nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
          nlinarith [h7, h8, h9]
        rw [← h2]
        field_simp [Real.sqrt_sq h6]
      rw [h1]
      all_goals norm_num
      <;> ring_nf <;> norm_num
      <;> ring