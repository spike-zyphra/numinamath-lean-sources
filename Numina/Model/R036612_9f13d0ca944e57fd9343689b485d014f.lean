import Mathlib

open Real

theorem algebra_277089 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a * b * (a + b) = 4) :
    2 * a + b ≥ 2 * sqrt 3 ∧ ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a * b * (a + b) = 4 ∧ 2 * a + b = 2 * sqrt 3 := by
  have h1 : (2 * a + b) ^ 2 ≥ 12 := by
    nlinarith [sq_nonneg (a - (Real.sqrt 3 - 1)), sq_nonneg (b - 2),
      sq_nonneg (a ^ 2 - (Real.sqrt 3 - 1) ^ 2), sq_nonneg (b - 2), 
      sq_nonneg ((2 * a + b) ^ 2 - (2 * Real.sqrt 3) ^ 2), 
      sq_nonneg (a * b), 
      h, 
      Real.sqrt_nonneg 3, 
      Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
      ]
  have h2 : 2 * a + b ≥ 2 * Real.sqrt 3 := by
    have h3 : (2 * a + b) ^ 2 ≥ 12 := h1
    have h4 : (2 * Real.sqrt 3) ^ 2 = 12 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    have h5 : (2 * a + b) ^ 2 ≥ (2 * Real.sqrt 3) ^ 2 := by
      linarith [h3, h4]
    have h6 : 0 ≤ 2 * a + b := by nlinarith
    have h7 : 0 ≤ 2 * Real.sqrt 3 := by nlinarith [Real.sqrt_nonneg 3]
    nlinarith [sq_nonneg ((2 * a + b) - 2 * Real.sqrt 3)]
  have h3 : ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a * b * (a + b) = 4 ∧ 2 * a + b = 2 * sqrt 3 := by
    use (Real.sqrt 3 - 1), 2
    constructor
    · -- Show $0 < a$
      nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    constructor
    · -- Show $0 < b$
      nlinarith
    constructor
    · -- Show $a \cdot b \cdot (a + b) = 4$
      nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    · -- Show $2 * a + b = 2 * sqrt 3$
      nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
  exact ⟨h2, h3⟩