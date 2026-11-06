import Mathlib

theorem algebra_310859 {x : ℝ} (hx : x = Real.sqrt (5 - Real.sqrt 5 - Real.sqrt (3 - Real.sqrt (29 - 12 * Real.sqrt 5)))) :
    x / Real.sqrt (3 - Real.sqrt (29 - 12 * Real.sqrt 5)) = 1 := by

  have h1 : Real.sqrt (29 - 12 * Real.sqrt 5) = 2 * Real.sqrt 5 - 3 := by
    have h2 : Real.sqrt (29 - 12 * Real.sqrt 5) = 2 * Real.sqrt 5 - 3 := by
      have h3 : (2 * Real.sqrt 5 - 3 : ℝ) ^ 2 = (29 - 12 * Real.sqrt 5 : ℝ) := by
        nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by linarith)]
      have h4 : (2 * Real.sqrt 5 - 3 : ℝ) ≥ 0 := by
        nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by linarith), show Real.sqrt 5 ≥ Real.sqrt 4 by apply Real.sqrt_le_sqrt (by norm_num)]
      rw [←h3]
      field_simp [Real.sqrt_sq (show (2 * Real.sqrt 5 - 3 : ℝ) ≥ 0 by linarith)]
    exact h2
  
  have h2 : Real.sqrt (3 - Real.sqrt (29 - 12 * Real.sqrt 5)) = Real.sqrt 5 - 1 := by
    rw [h1]
    have h3 : 3 - (2 * Real.sqrt 5 - 3 : ℝ) = (6 - 2 * Real.sqrt 5 : ℝ) := by
      nlinarith
    have h4 : Real.sqrt (3 - (2 * Real.sqrt 5 - 3 : ℝ)) = Real.sqrt (6 - 2 * Real.sqrt 5 : ℝ) := by 
      rw [h3]
    have h5 : Real.sqrt (6 - 2 * Real.sqrt 5 : ℝ) = Real.sqrt 5 - 1 := by
      have h51 : (Real.sqrt 5 - 1 : ℝ) ^ 2 = (6 - 2 * Real.sqrt 5 : ℝ) := by
        nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by linarith)]
      have h52 : (Real.sqrt 5 - 1 : ℝ) ≥ 0 := by
        nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by linarith), show (1 : ℝ) ≤ Real.sqrt 5 by nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by linarith), (show (1 : ℝ) ^ 2 < (5 : ℝ) by nlinarith) ] ]
      rw [←h51]
      field_simp [Real.sqrt_sq (show (Real.sqrt 5 - 1 : ℝ) ≥ 0 by linarith)]
      all_goals nlinarith
    rw [h4, h5]

  have h3 : x = Real.sqrt 5 - 1 := by
    rw [hx]
    have h8 : Real.sqrt (5 - Real.sqrt 5 - Real.sqrt (3 - Real.sqrt (29 - 12 * Real.sqrt 5)) ) = Real.sqrt 5 - 1 := by
      have h4 : 5 - Real.sqrt 5 - Real.sqrt (3 - Real.sqrt (29 - 12 * Real.sqrt 5)) = (6 - 2 * Real.sqrt 5 : ℝ) := by 
        rw [h2]
        nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by linarith)]
      rw [h4]
      have h81 : (Real.sqrt 5 - 1 : ℝ) ^ 2 = (6 - 2 * Real.sqrt 5 : ℝ) := by
        nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by linarith)]
      have h82 : (Real.sqrt 5 - 1 : ℝ) ≥ 0 := by
        nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by linarith), show (1 : ℝ) ≤ Real.sqrt 5 by nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by linarith), (show (1 : ℝ) ^ 2 < (5 : ℝ) by nlinarith) ] ]
      rw [←h81]
      field_simp [Real.sqrt_sq (show (Real.sqrt 5 - 1 : ℝ) ≥ 0 by linarith)]
      all_goals nlinarith
    exact h8
  
  have h4 : Real.sqrt (3 - Real.sqrt (29 - 12 * Real.sqrt 5)) = Real.sqrt 5 - 1 := h2
  
  rw [h3, h4]
  have h7 : Real.sqrt 5 - 1 > 0 := by
    nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by linarith), show (1 : ℝ) < Real.sqrt 5 by nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by linarith), (show (1 : ℝ) ^ 2 < (5 : ℝ) by nlinarith) ] ]
  have h8 : Real.sqrt 5 - 1 ≠ 0 := by linarith [h7]
  field_simp [h8]