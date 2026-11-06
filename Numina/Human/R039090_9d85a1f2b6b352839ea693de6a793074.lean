import Mathlib

open Real

theorem algebra_160164 {x : ℝ} (hx : x = 3) :
    sqrt (x - 2 * sqrt 2) / sqrt (x^2 - 4 * x * sqrt 2 + 8) -
    sqrt (x + 2 * sqrt 2) / sqrt (x^2 + 4 * x * sqrt 2 + 8) = 2 := by
  -- x - 2 √2 = (√2 - 1) ^ 2
  have h1 : x - 2 * sqrt 2 = (sqrt 2 - 1) ^ 2 := by
    rw [hx]
    have h2 : (3 : ℝ) - 2 * sqrt 2 = (sqrt 2 - 1) ^ 2 := by
      calc
        (3 : ℝ) - 2 * sqrt 2 = (sqrt 2) ^ 2 - 2 * sqrt 2 + 1 := by
          have h21 : (sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
          linarith [h21]
        _ = (sqrt 2 - 1) ^ 2 := by
          ring
    linarith [h2]
  -- √ (x - 2 √ 2) =  √ 2 - 1
  have h2 : sqrt (x - 2 * sqrt 2) = sqrt 2 - 1 := by
    rw [h1]
    rw [Real.sqrt_sq]
    have h21 : 1 < sqrt 2 := Real.lt_sqrt_of_sq_lt (by norm_num)
    have h22 : sqrt 2 - 1 ≥ 0 := by linarith
    all_goals linarith
  -- x ^ 2 - 4√2 x + 8 = (3 - 2 * √2) ^ 2
  have h3 : x^2 - 4 * x * sqrt 2 + 8 = (3 - 2 * sqrt 2) ^ 2 := by
    rw [hx]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  -- √ (x^2 - 4 √2 x + 8) = 3 - 2 * √2
  have h4 : sqrt (x^2 - 4 * x * sqrt 2 + 8) = 3 - 2 * sqrt 2 := by
    rw [h3]
    rw [Real.sqrt_sq]
    have h41 : 3 - 2 * sqrt 2 ≥ 0 := by
      have h411 : sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
      nlinarith [Real.sqrt_nonneg (2 : ℝ), sq_nonneg (sqrt 2 - 3 / 2)]
    all_goals linarith
  -- x + 2 √2 = (√2 + 1) ^ 2
  have h5 : x + 2 * sqrt 2 = (sqrt 2 + 1) ^ 2 := by
    rw [hx]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  -- √(x + 2√2) = √2 + 1
  have h6 : sqrt (x + 2 * sqrt 2) = sqrt 2 + 1 := by
    rw [h5]
    rw [Real.sqrt_sq]
    have h61 : sqrt 2 + 1 ≥ 0 := by
      have h611 : sqrt 2 ≥ 0 := Real.sqrt_nonneg 2
      linarith
    all_goals linarith
  -- x ^ 2 + 4√2 x + 8 = (3 + 2 * √2) ^ 2
  have h7 : x^2 + 4 * x * sqrt 2 + 8 = (3 + 2 * sqrt 2) ^ 2 := by
    rw [hx]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  -- √ (x^2 + 4 √2 x + 8) = 3 + 2 * √2
  have h8 : sqrt (x^2 + 4 * x * sqrt 2 + 8) = 3 + 2 * sqrt 2 := by
    rw [h7]
    rw [Real.sqrt_sq]
    have h81 : 3 + 2 * sqrt 2 ≥ 0 := by
      nlinarith [Real.sqrt_nonneg 2]
    all_goals linarith
  rw [h2, h4, h6, h8]
  --  ( √2 - 1 ) / (3 - 2 * √2) - (√2 + 1) / (3 + 2 * √2) = 2
  have h9 : (sqrt 2 - 1) / (3 - 2 * sqrt 2) - (sqrt 2 + 1) / (3 + 2 * sqrt 2) = 2 := by
    have denom1_pos : 3 - 2 * sqrt 2 ≠ 0 := by
      have h1 : 3 - 2 * sqrt 2 > 0 := by
        have h21 : sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
        nlinarith [Real.sqrt_nonneg (2 : ℝ), sq_nonneg (sqrt 2 - 3 / 2)]
      linarith
    have denom2_pos : 3 + 2 * sqrt 2 ≠ 0 := by
      have h1 : 3 + 2 * sqrt 2 > 0 := by nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num : (2 : ℝ) > 0)]
      linarith
    field_simp [denom1_pos, denom2_pos]
    <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2, mul_self_nonneg (sqrt 2 - 1), mul_self_nonneg (sqrt 2 + 1), mul_self_nonneg (sqrt 2 - 3 / 2), mul_self_nonneg (sqrt 2 - 3 / 2)]
  linarith [h9]