import Mathlib

theorem algebra_238191 {a b : ℝ} (h : (a + Real.sqrt (1 + a ^ 2)) * (b + Real.sqrt (1 + b ^ 2)) = 1) :
    a + b = 0 := by
  have hapos: a + Real.sqrt (1 + a ^ 2) ≠ 0 := by
    intro h'; rw [h'] at h; linarith
  have hbpos: b + Real.sqrt (1 + b ^ 2) ≠ 0 := by
    intro h'; rw [h'] at h; linarith
  have h1 : a + Real.sqrt (1 + a ^ 2) = Real.sqrt (1 + b ^ 2) - b := by
    have eq5 : (a + Real.sqrt (1 + a ^ 2)) = (b + Real.sqrt (1 + b ^ 2))⁻¹ := by
      have eq6 : (a + Real.sqrt (1 + a ^ 2)) * (b + Real.sqrt (1 + b ^ 2)) = 1 := by linarith
      have h2 : b + Real.sqrt (1 + b ^ 2) ≠ 0 := hbpos
      field_simp at *
      all_goals nlinarith
    have eq6 : (b + Real.sqrt (1 + b ^ 2))⁻¹ = Real.sqrt (1 + b ^ 2) - b := by
      have eq7 : (b + Real.sqrt (1 + b ^ 2)) * (Real.sqrt (1 + b ^ 2) - b) = 1 := by
        nlinarith [Real.sqrt_nonneg (1 + b ^ 2), Real.sq_sqrt (show (0 : ℝ) ≤ 1 + b ^ 2 by nlinarith)]
      have eq8 : (b + Real.sqrt (1 + b ^ 2)) * (Real.sqrt (1 + b ^ 2) - b) = 1 := by linarith [eq7]
      have h2 : b + Real.sqrt (1 + b ^ 2) ≠ 0 := hbpos
      field_simp at *
      all_goals nlinarith
    rw [eq5]
    exact eq6
  -- Prove that `b + Real.sqrt (1 + b ^ 2) = Real.sqrt (1 + a ^ 2) - a`.
  have h2 : b + Real.sqrt (1 + b ^ 2) = Real.sqrt (1 + a ^ 2) - a := by
    have eq5' : (b + Real.sqrt (1 + b ^ 2)) = (a + Real.sqrt (1 + a ^ 2))⁻¹ := by
      have eq6' : (a + Real.sqrt (1 + a ^ 2)) * (b + Real.sqrt (1 + b ^ 2)) = 1 := by linarith
      have h3 : a + Real.sqrt (1 + a ^ 2) ≠ 0 := hapos
      field_simp at *
      all_goals nlinarith
    have eq6' : (a + Real.sqrt (1 + a ^ 2))⁻¹ = Real.sqrt (1 + a ^ 2) - a := by
      have eq7 : (a + Real.sqrt (1 + a ^ 2)) * (Real.sqrt (1 + a ^ 2) - a) = 1 := by
        nlinarith [Real.sqrt_nonneg (1 + a ^ 2), Real.sq_sqrt (show (0 : ℝ) ≤ 1 + a ^ 2 by nlinarith)]
      have eq8 : (a + Real.sqrt (1 + a ^ 2)) * (Real.sqrt (1 + a ^ 2) - a) = 1 := by linarith [eq7]
      have h10 : a + Real.sqrt (1 + a ^ 2) ≠ 0 := hapos
      field_simp at *
      all_goals nlinarith
    rw [eq5']
    exact eq6'
  -- From `h1` and `h2`, derive `a + b = 0`.
  have ht1 : a + b = 0 := by
    nlinarith [Real.sqrt_nonneg (1 + a ^ 2), Real.sqrt_nonneg (1 + b ^ 2), 
      Real.sq_sqrt (show (0 : ℝ) ≤ 1 + a ^ 2 by nlinarith), 
      Real.sq_sqrt (show (0 : ℝ) ≤ 1 + b ^ 2 by nlinarith)
    ]
  linarith