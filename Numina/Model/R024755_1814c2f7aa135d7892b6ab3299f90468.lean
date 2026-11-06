import Mathlib

open Real
open scoped BigOperators

theorem inequalities_110441 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (hle : a ≤ b ∧ b < c) (h : a^2 + b^2 = c^2) :
  1 / a + 1 / b + 1 / c ≥ (5 + 3 * sqrt 2) / (a + b + c) := by
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc

  have h2 : a + b + c > 0 := by
    linarith [ha, hb, hc]

  have h3 : 1 / a + 1 / b + 1 / c - (5 + 3 * sqrt 2) / (a + b + c) ≥ 0 := by
    have h4 : (1 / a + 1 / b + 1 / c - (5 + 3 * sqrt 2) / (a + b + c)) =
          (b * c * (a + b + c) + a * c * (a + b + c) + a * b * (a + b + c) - (5 + 3 * sqrt 2) * (a * b * c)) / (a * b * c * (a + b + c)) := by
      field_simp
      ring

    rw [h4] at *
    have h5 : 0 < a * b * c * (a + b + c) := by
      positivity

    have h6 : b * c * (a + b + c) + a * c * (a + b + c) + a * b * (a + b + c) - (5 + 3 * sqrt 2) * (a * b * c) ≥ 0 := by
      have h9 : 0 < a * b := mul_pos ha hb
      have h10 : c > b := by nlinarith [h, sq_pos_of_pos hb, hle.2]
      have h11 : (c - b) > 0 := by linarith [h10]
      nlinarith [sq_nonneg (a - b), sq_nonneg (a * (a - b)), sq_nonneg (b * (a - b)), 
        sq_nonneg (c - a - b), sq_nonneg (c - a * Real.sqrt 2), sq_nonneg (c - b * Real.sqrt 2), 
        Real.sqrt_nonneg (2), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), 
        sq_nonneg (a^2 + b^2 - c^2), 
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
        sq_nonneg (a - b), 
        Real.sqrt_nonneg (2), 
        mul_nonneg (show 0 ≤ (a: ℝ) by linarith) (show 0 ≤ (b: ℝ) by linarith), 
        hle.1, 
        mul_nonneg (show 0 ≤ (a: ℝ) by linarith) (show 0 ≤ (c: ℝ) by linarith), 
        mul_nonneg (show 0 ≤ (b: ℝ) by linarith) (show 0 ≤ (c: ℝ) by linarith), 
        mul_nonneg (show 0 ≤ (a: ℝ) by linarith) (show 0 ≤ (a * b: ℝ) by nlinarith), 
        mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
        mul_nonneg (show 0 ≤ a by linarith) (show (0 : ℝ) ≤ b by linarith)
      ]

    apply div_nonneg
    linarith [h6]
    all_goals positivity

  linarith [h3]