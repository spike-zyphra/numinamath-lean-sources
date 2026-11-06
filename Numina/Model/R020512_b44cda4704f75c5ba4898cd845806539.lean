import Mathlib

theorem algebra_214952 {a : ℝ} (ha : a ≠ 0) (h : a / Real.sqrt 6 + Real.sqrt 6 / a = 5) :
    (a ^ 8 + 1296) / (36 * a ^ 4) = 527 := by 

  have h1 : a / Real.sqrt 6 + Real.sqrt 6 / a = 5 := h 
  have eq1 : a ^ 2 + 6 = 5 * a * Real.sqrt 6 := by 
    have eq2 : a / Real.sqrt 6 + Real.sqrt 6 / a = (a ^ 2 + 6) / (a * Real.sqrt 6) := by
      field_simp [show Real.sqrt 6 > 0 by positivity, ha]
      <;> ring 
    rw [eq2] at h 
    have eq3 : (a ^ 2 + 6 : ℝ) / (a * Real.sqrt 6) = 5 := h 
    have eq4 : a * Real.sqrt 6 ≠ 0 := by
      apply mul_ne_zero 
      exact ha 
      positivity 
    have eq5 : a ^ 2 + 6 = 5 * (a * Real.sqrt 6) := by 
      field_simp at eq3 
      linarith 
    linarith 

  have eq5 : (a ^ 2 + 6) ^ 2 = 150 * a ^ 2 := by 
    have eq6 : (a ^ 2 + 6) ^ 2 = (5 * a * Real.sqrt 6) ^ 2 := by 
      rw [show a ^ 2 + 6 = 5 * a * Real.sqrt 6 by linarith [eq1]]
    have eq8 : (5 * a * Real.sqrt 6) ^ 2 = 150 * a ^ 2 := by 
      have h6 : Real.sqrt 6 ^ 2 = 6 := by 
        rw [Real.sq_sqrt] 
        all_goals norm_num 
      calc 
        (5 * a * Real.sqrt 6) ^ 2 = (5 * a) ^ 2 * (Real.sqrt 6) ^ 2 := by ring
        _ = (5 * a) ^ 2 * 6 := by 
          rw [h6] 
        _ = 25 * a ^ 2 * 6 := by 
          ring 
        _ = 150 * a ^ 2 := by 
          ring 
    rw [eq6, eq8] 

  have eq6 : a ^ 4 - 138 * a ^ 2 + 36 = 0 := by 
    nlinarith [eq5] 

  have eq8 : a ^ 4 = 138 * a ^ 2 - 36 := by 
    linarith [eq6] 
  have eq9 : a ^ 8 = (a ^ 4) ^ 2 := by 
    ring 
  have eq11 : a ^ 8 = (138 * a ^ 2 - 36) ^ 2 := by 
    rw [eq9, eq8] 

  have eq10 : (a ^ 8 + 1296) / (36 * a ^ 4) = 527 := by 
    field_simp [(show a ^ 4 ≠ 0 by
      by_contra h'
      have h'1 : a ^ 4 = 0 := by
        linarith [h']
      have h'2 : a ^ 2 = 0 := by
        nlinarith [sq_nonneg a]
      have h'3 : a = 0 := by
        nlinarith [sq_nonneg a]
      contradiction
    )]
    nlinarith [Real.sqrt_nonneg (6 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num), sq_nonneg (a ^ 2 - 24), sq_nonneg (a ^ 2 - 24)]
  exact eq10