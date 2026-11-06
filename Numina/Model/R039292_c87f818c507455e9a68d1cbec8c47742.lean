import Mathlib

theorem algebra_288669 {x y : ℝ} (h1 : Real.sqrt (11 * x - y) - Real.sqrt (y - x) = 1)
    (h2 : 7 * Real.sqrt (y - x) + 6 * y - 26 * x = 3) :
    x = 0.5 ∧ y = 1.5 := by
  -- Show expressions positive
  have h4 : 0 ≤ 11 * x - y := by
    by_contra h
    push_neg at h
    have h5 : Real.sqrt (11 * x - y) = 0 := by
      rw [Real.sqrt_eq_zero']
      linarith
      all_goals nlinarith
    have h6 : Real.sqrt (11 * x - y) - Real.sqrt (y - x) =1 := h1
    rw [h5] at h6
    have h7 : Real.sqrt (y - x) = -1 := by linarith
    have h8 : Real.sqrt (y - x) ≥ 0 := by
      apply Real.sqrt_nonneg
    nlinarith [show Real.sqrt (y - x) ≥ 0 by apply Real.sqrt_nonneg]
  -- Show expressions positive
  have h5 : 0 ≤ y - x := by
    by_contra h
    push_neg at h
    have h6 : Real.sqrt (y - x) = 0 := by
      rw [Real.sqrt_eq_zero']
      linarith
      all_goals nlinarith
    have h7 : Real.sqrt (11 * x - y) - Real.sqrt (y - x) =1 := h1
    rw [h6] at h7
    have h8 : Real.sqrt (11 * x - y) = 1 := by linarith
    have h9 : 11 * x - y = 1 := by
      calc
        11 * x - y = (Real.sqrt (11 * x - y)) ^ 2 := by
          rw [Real.sq_sqrt]
          nlinarith
        _ = 1 ^ 2 := by
          rw [h8]
        _ = (1 : ℝ) := by norm_num
    nlinarith
  -- Now squared expressions substituted
  have h63 : Real.sqrt (11 * x - y) = 1 + Real.sqrt (y - x) := by linarith
  -- Now manipulations
  have eq3 : Real.sqrt (11 * x - y) ^ 2 = 11 * x - y := by
    apply Real.sq_sqrt
    linarith
  have eq4 : Real.sqrt (y - x) ^ 2 = y - x := by
    apply Real.sq_sqrt
    linarith
  -- Solve system manipulating to
  have eq6 : Real.sqrt (11 * x - y) ^ 2 = (1 + Real.sqrt (y - x)) ^ 2 := by
    rw [show Real.sqrt (11 * x - y) = 1 + Real.sqrt (y - x) by linarith]
  rw [eq3] at eq6
  have eq5 : (1 + Real.sqrt (y - x)) ^ 2 = 1 + 2 * Real.sqrt (y - x) + (Real.sqrt (y - x) ^ 2) := by
    ring
  rw [eq5] at eq6
  rw [eq4] at eq6
  have eq6 : Real.sqrt (y - x) = (6 * x - y - 0.5 : ℝ) := by
    nlinarith
  have ht1 : (Real.sqrt (y - x) ) ^ 2 = (6 * x - y - 0.5 : ℝ) ^ 2 := by 
    rw [eq6]
  rw [eq4] at ht1
  -- The final problem integral pair of points.
  have eq12 : x = 0.5 := by
    nlinarith [Real.sqrt_nonneg (11 * x - y), Real.sqrt_nonneg (y - x), sq_nonneg (Real.sqrt (y - x) - (6 * x - y - 0.5 : ℝ)), sq_nonneg (y - 1.5 : ℝ), sq_nonneg (x - 0.5 : ℝ)]
  have eq14 : y = 1.5 := by
    nlinarith [eq12, Real.sqrt_nonneg (11 * x - y), Real.sqrt_nonneg (y - x)]
  exact ⟨eq12, eq14⟩