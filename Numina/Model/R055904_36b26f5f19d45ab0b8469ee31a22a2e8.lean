import Mathlib

theorem algebra_170732 (x : ℝ) :
    (x^2 + 3 * x + 2) * (x^2 - 7 * x + 12) * (x^2 - 2 * x - 1) + 24 = 0 ↔
    x = 0 ∨ x = 2 ∨ x = 1 + Real.sqrt 6 ∨ x = 1 - Real.sqrt 6 ∨ x = 1 + 2 * Real.sqrt 2 ∨
    x = 1 - 2 * Real.sqrt 2 := by
  constructor
  · -- Assume left side, prove right side
    intro h
    have h1 : (x^2 + 3 * x + 2) * (x^2 - 7 * x + 12) * (x^2 - 2 * x - 1) + 24 = 0 := h
    have h2 : x * (x - 2) * (x^2 - 2 * x - 7) * (x^2 - 2 * x - 5) = 0 := by
      nlinarith [sq_nonneg (x ^ 2 - 2 * x - 1), sq_nonneg (x ^ 2 - 2 * x - 7), sq_nonneg (x ^ 2 - 2 * x - 5), sq_nonneg (x), sq_nonneg (x - 2)]
    cases' (mul_eq_zero.mp h2) with h3 h4
    cases' (mul_eq_zero.mp h3) with h5 h6
    cases' (mul_eq_zero.mp h5) with h7 h8
    · -- x = 0
      left
      linarith
    · -- x - 2 = 0, so x = 2
      right
      left
      linarith
    · -- x^2 - 2x - 7 = 0
      have h9 : x^2 - 2 * x - 7 = 0 := h6
      have h11 : x^2 - 2 * x - 7 = (x - (1 + 2 * Real.sqrt 2)) * (x - (1 - 2 * Real.sqrt 2)) := by
        nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2]
      rw [h11] at h9
      cases' (mul_eq_zero.mp h9) with h12 h13
      · -- x - (1 + 2 * sqrt 2) = 0
        right
        right
        right
        right
        left
        linarith
      · -- x - (1 - 2 * sqrt 2) = 0
        right
        right
        right
        right
        right
        linarith
    · -- x^2 - 2 * x - 5 = 0
      have h14 : x^2 - 2 * x - 5 = 0 := h4
      have h16 : x^2 - 2 * x - 5 = (x - (1 + Real.sqrt 6)) * (x - (1 - Real.sqrt 6)) := by
        nlinarith [Real.sq_sqrt (show 0 ≤ (6 : ℝ) by norm_num), Real.sqrt_nonneg 6]
      rw [h16] at h14
      cases' (mul_eq_zero.mp h14) with h17 h18
      · -- x - (1 + sqrt 6) = 0
        right
        right
        left
        linarith
      · -- x - (1 - sqrt 6) = 0
        right
        right
        right
        left
        linarith
  · -- Assume right side, prove left side
    rintro (h | h | h | h | h | h)
    · -- x = 0
      rw [h]
      norm_num
    · -- x = 2
      rw [h]
      norm_num
    · -- x = 1 + sqrt 6
      rw [h]
      nlinarith [Real.sq_sqrt (show 0 ≤ (6 : ℝ) by norm_num), Real.sqrt_nonneg 6, 
        sq_nonneg ((1 + Real.sqrt 6) ^ 2 - 2 * (1 + Real.sqrt 6) - 1), 
        sq_nonneg ((1 + Real.sqrt 6) ^ 2 - 7 * (1 + Real.sqrt 6) + 12), 
        sq_nonneg ((1 + Real.sqrt 6) ^ 2 + 3 * (1 + Real.sqrt 6) + 2)
      ]
    · -- x = 1 - sqrt 6
      rw [h]
      nlinarith [Real.sq_sqrt (show 0 ≤ (6 : ℝ) by norm_num), Real.sqrt_nonneg 6, 
        sq_nonneg ((1 - Real.sqrt 6) ^ 2 - 2 * (1 - Real.sqrt 6) - 1), 
        sq_nonneg ((1 - Real.sqrt 6) ^ 2 - 7 * (1 - Real.sqrt 6) + 12), 
        sq_nonneg ((1 - Real.sqrt 6) ^ 2 + 3 * (1 - Real.sqrt 6) + 2)
      ]
    · -- x = 1 + 2 * sqrt 2
      rw [h]
      nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, 
        sq_nonneg ((1 + 2 * Real.sqrt 2) ^ 2 - 2 * (1 + 2 * Real.sqrt 2) - 1), 
        sq_nonneg ((1 + 2 * Real.sqrt 2) ^ 2 - 7 * (1 + 2 * Real.sqrt 2) + 12), 
        sq_nonneg ((1 + 2 * Real.sqrt 2) ^ 2 + 3 * (1 + 2 * Real.sqrt 2) + 2)
      ]
    · -- x = 1 - 2 * sqrt 2
      rw [h]
      nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sqrt_nonneg 2, 
        sq_nonneg ((1 - 2 * Real.sqrt 2) ^ 2 - 2 * (1 - 2 * Real.sqrt 2) - 1), 
        sq_nonneg ((1 - 2 * Real.sqrt 2) ^ 2 - 7 * (1 - 2 * Real.sqrt 2) + 12), 
        sq_nonneg ((1 - 2 * Real.sqrt 2) ^ 2 + 3 * (1 - 2 * Real.sqrt 2) + 2)
      ]