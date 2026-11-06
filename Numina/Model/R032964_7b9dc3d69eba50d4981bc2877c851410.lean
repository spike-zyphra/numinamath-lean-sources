import Mathlib

open Real

theorem algebra_185013 {x : ℝ} (hx : x = 2 * sqrt (61 + 24 * sqrt 5)) :
    (4 / (3 - sqrt 5))^2 - (6 - 5 * sqrt 6)^2 / (5 - sqrt 6)^2 = x := by
  have h1 : sqrt 5 > 0 := by
    apply Real.sqrt_pos.2
    all_goals norm_num

  have h5 : sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by linarith)

  have h6 : sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by linarith)

  have h7 : sqrt (61 + 24 * sqrt 5) = 3 * sqrt 5 + 4 := by
    have h8 : (3 * sqrt 5 + 4) ^ 2 = 61 + 24 * sqrt 5 := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
    have h9 : 0 ≤ (3 * sqrt 5 + 4 : ℝ) := by
      positivity
    have h10 : (61 + 24 * sqrt 5) ≥ 0 := by
      positivity
    have h11 : sqrt (61 + 24 * sqrt 5) = 3 * sqrt 5 + 4 := by
      rw [← h8]
      field_simp [Real.sqrt_sq, h9]
    linarith [h11]

  have h8 : x = 2 * (3 * sqrt 5 + 4) := by
    rw [hx, h7]

  have h9 : (4 / (3 - sqrt 5)) ^ 2 = (3 + sqrt 5) ^ 2 := by
    have h11 : (3 - sqrt 5) ≠ 0 := by
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
    have h12 : (4 / (3 - sqrt 5)) = (3 + sqrt 5) := by
      field_simp [h11]
      <;> 
      nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
    rw [h12]

  have h10 : (6 - 5 * sqrt 6) ^ 2 / (5 - sqrt 6) ^ 2 = (sqrt 6) ^ 2 := by
    have h13 : (6 - 5 * sqrt 6) / (5 - sqrt 6) = -sqrt 6 := by
      have h111 : (5 - sqrt 6) ≠ 0 := by
        nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]
      field_simp [h111]
      <;> 
      nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show 0 ≤ (6 : ℝ) by norm_num), sq_nonneg (sqrt 6 ^ 2)]
    have h14 : (6 - 5 * sqrt 6) ^ 2 / (5 - sqrt 6) ^ 2 = ((6 - 5 * sqrt 6) / (5 - sqrt 6)) ^ 2 := by
      field_simp [show (5 - sqrt 6 : ℝ) ≠ 0 by
        nlinarith [Real.sqrt_nonneg 6, Real.sq_sqrt (show 0 ≤ (6 : ℝ) by norm_num)]
      ]
    rw [h14, h13]
    <;> 
    ring_nf <;> 
    norm_num

  rw [h9, h10, h8]
  nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 6, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)]