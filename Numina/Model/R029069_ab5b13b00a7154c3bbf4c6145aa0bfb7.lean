import Mathlib

open Real
open scoped BigOperators

theorem inequalities_600748 {a b c h : ℝ}
  (ha : a > 0) (hb : b > 0) (hc : c > 0) (h₀ : a^2 + b^2 = c^2)
  (h₁ : h * c = a * b) -- this equation is for the height
  :
  2 * sqrt 2 / 3 * (c + h) ≤ a + b ∧ a + b < c + h := by

  have h2 : h > 0 := by
    nlinarith [h₀, h₁, mul_pos ha hb, sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]

  have h3 : a + b < c + h := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - (c + h)), sq_nonneg (c - (a + b)), sq_nonneg (c - h), 
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, h₀, h₁, mul_pos (show 0 < c by linarith) (show 0 < c by linarith)]

  have h4 : (a + b) ^ 2 ≥ 8 / 9 * (c + h) ^ 2 := by
    have h5 : (a + b) ^ 2 = c^2 + 2 * (h * c) := by
      nlinarith [h₀, h₁]
    have h6 : (c + h) ^ 2 = c^2 + 2 * (h * c) + h^2 := by 
      nlinarith 
    rw [h5]
    have h7 : c^2 + 2 * (h * c) ≥ 8 / 9 * (c + h) ^ 2 := by
      have h8 : c^2 + 2 * (h * c) - 8 / 9 * (c + h) ^ 2 ≥ 0 := by
        nlinarith [sq_nonneg (c - 2 * h), sq_nonneg (a - b), 
          h₀, h₁, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
      nlinarith
    nlinarith

  have h5 : 2 * sqrt 2 / 3 * (c + h) ≤ a + b := by
    have h8 : (2 * sqrt 2 / 3 * (c + h)) ^ 2 ≤ (a + b) ^ 2 := by
      nlinarith [h4, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (c - 2 * h)]
    have h9 : 2 * sqrt 2 / 3 * (c + h) ≥ 0 := by
      positivity
    have h10 : (a + b) ≥ 0 := by
      positivity
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), h8]

  constructor
  · exact h5
  · exact h3