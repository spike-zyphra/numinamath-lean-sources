import Mathlib

theorem algebra_1991 {x : ℝ} (hx : 0 ≤ x) (y : ℝ) (hy : y = Real.sqrt (2 * x)) :
    Real.sqrt (y + 5) + Real.sqrt (y - 3) = 4 ↔ x = 8 := by 
  constructor
  · -- Assume $\sqrt{y + 5} + \sqrt{y - 3} = 4$, prove $x = 8$
    intro h_eq
    have h1 : Real.sqrt (y + 5) ≥ 0 := by positivity
    have h2 : Real.sqrt (y - 3) ≥ 0 := by positivity

    have h4 : y + 5 ≥ 0 := by 
      by_contra h 
      push_neg at h 
      have h5 : Real.sqrt (y + 5) = 0 := by
        rw [Real.sqrt_eq_zero']
        linarith 
      rw [h5] at h_eq 
      have h6 : Real.sqrt (y - 3) = 4 := by linarith 
      by_cases h7 : (y - 3) ≥ 0 
      · -- case `y - 3 ≥ 0`: apply `Real.sq_sqrt` and derive contradiction with `h`
        have h8 : (Real.sqrt (y - 3)) ^ 2 = y - 3 := Real.sq_sqrt (show (y - 3 : ℝ) ≥ (0 : ℝ) by linarith)
        have h9 : y - 3 = 16 := by 
          calc 
            y - 3 = (Real.sqrt (y - 3)) ^ 2 := by linarith [h8]
            _ = (4 : ℝ) ^ 2 := by rw [h6]
            _ = (16 : ℝ) := by norm_num 
        have h10 : y = 19 := by linarith 
        nlinarith [Real.sq_sqrt (show (y + 5 : ℝ) ≥ 0 by linarith), h5, h10]
      · -- case `y - 3 < 0`: also leads to contradiction 
        have h8 : (y - 3) < 0 := by linarith 
        have h9 : Real.sqrt (y - 3) = 0 := by
          rw [Real.sqrt_eq_zero']
          linarith
        rw [h9] at h6
        all_goals linarith

    have h8 : y - 3 ≥ 0 := by 
      by_contra h9
      push_neg at h9
      have h9' : (Real.sqrt (y - 3)) = 0 := by
        rw [Real.sqrt_eq_zero']
        linarith
      rw [h9'] at h_eq
      have h5 : Real.sqrt (y + 5) = 4 := by linarith
      have h11 : y + 5 = 16 := by
        calc
          y + 5 = (Real.sqrt (y + 5)) ^ 2 := by rw [Real.sq_sqrt]; all_goals linarith
          _ = (4 : ℝ) ^ 2 := by rw [h5]
          _ = 16 := by norm_num
      have hy2 : y = 11 := by linarith
      nlinarith [Real.sq_sqrt (show (y + 5 : ℝ) ≥ 0 by linarith), h5, Real.sq_sqrt (show (y - 3 : ℝ) ≥ 0 by linarith), h9', hy2]

    have h3 : Real.sqrt (y + 5) = 4 - Real.sqrt (y - 3) := by linarith 
    have h5 : (Real.sqrt (y + 5)) ^ 2 = (4 - Real.sqrt (y - 3)) ^ 2 := by
      rw [h3]
    have h6 : (Real.sqrt (y + 5)) ^ 2 = y + 5 := by 
      apply Real.sq_sqrt 
      linarith 
    have h7 : (4 - Real.sqrt (y - 3)) ^ 2 = 16 - 8 * Real.sqrt (y - 3) + (Real.sqrt (y - 3)) ^ 2 := by 
      ring
    have h8 : (Real.sqrt (y - 3)) ^ 2 = y - 3 := by 
      apply Real.sq_sqrt 
      linarith
    have h9 : y = 4 := by 
      nlinarith [Real.sqrt_nonneg (y + 5), Real.sqrt_nonneg (y - 3), 
        h6, h7, h8, h5, Real.sq_sqrt (show (y + 5) ≥ 0 by linarith), Real.sq_sqrt (show (y - 3) ≥ 0 by linarith)]
    have h9 : 2 * x = 16 := by
      have h10 : (Real.sqrt (2 * x)) ^ 2 = 16 := by
        have : Real.sqrt (2 * x) = 4 := by
          linarith [h9, hy]
        rw [this]
        norm_num
      have h11 : (Real.sqrt (2 * x)) ^ 2 = 2 * x := by
        rw [Real.sq_sqrt]
        nlinarith
      nlinarith [h10, h11]
    have hx8 : x = 8 := by 
      nlinarith
    linarith
  · -- Assume x = 8, prove sqrt(y + 5) + sqrt(y - 3) = 4
    intro h_eq
    have hx8 : x = 8 := h_eq
    have hy4 : y = 4 := by
      rw [hy]
      have h9 : Real.sqrt (2 * x) = 4 := by
        rw [hx8]
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      linarith [h9]
    have h_eq1 : Real.sqrt (y + 5) + Real.sqrt (y - 3) = 4 := by
      rw [hy4]
      have h10 : Real.sqrt ( (4 : ℝ) + 5 ) = 3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h11 : Real.sqrt ( (4 : ℝ) - 3 ) = 1 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      rw [h10, h11]
      all_goals norm_num
    linarith [h_eq1]