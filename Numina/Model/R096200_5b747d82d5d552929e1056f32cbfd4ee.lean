import Mathlib

theorem algebra_177973 (x : ℝ) (hx : x ≥ -1) :
    2.55 * Real.sqrt (x + 1) + Real.sqrt (4 * x + 13) = Real.sqrt (3 * x + 12) ↔ x = -1 := by 
  constructor
  · -- Forward direction: if equation holds, then x = -1
    intro h_eq
    have h1 : 2.55 * Real.sqrt (x + 1) + Real.sqrt (4 * x + 13) = Real.sqrt (3 * x + 12) := h_eq
    have h2 : (2.55 * Real.sqrt (x + 1) + Real.sqrt (4 * x + 13)) ^ 2 = (Real.sqrt (3 * x + 12)) ^ 2 := by
      rw [h1]
    have h3 : 0 ≤ (x + 1 : ℝ) := by linarith [hx]
    have h4 : 0 ≤ (4 * x + 13 : ℝ) := by 
      nlinarith [hx]
    have h5 : 0 ≤ (3 * x + 12 : ℝ) := by
      nlinarith [hx]
    have eq1 : (2.55 * Real.sqrt (x + 1) + Real.sqrt (4 * x + 13)) ^ 2 =
      (2.55 * Real.sqrt (x + 1)) ^ 2 + (Real.sqrt (4 * x + 13)) ^ 2 + 2 * (2.55 * Real.sqrt (x + 1) * Real.sqrt (4 * x + 13)) := by ring
    have eq2 : (Real.sqrt (3 * x + 12)) ^ 2 = 3 * x + 12 := by
      rw [Real.sq_sqrt]
      linarith
    have eq3 : (2.55 * Real.sqrt (x + 1)) ^ 2 = (2.55 : ℝ) ^ 2 * (Real.sqrt (x + 1)) ^ 2 := by ring
    have eq4 : (Real.sqrt (4 * x + 13)) ^ 2 = 4 * x + 13 := by 
      rw [Real.sq_sqrt]
      linarith
    have eq5 : Real.sqrt (x + 1) * Real.sqrt (4 * x + 13) = Real.sqrt ((x + 1) * (4 * x + 13)) := by
      rw [← Real.sqrt_mul (by nlinarith)]
    have eq6 : (Real.sqrt (x + 1)) ^ 2 = x + 1 := by 
      rw [Real.sq_sqrt]
      linarith
    rw [eq1, eq2, eq3, eq4, eq6] at h2
    -- h2 becomes 
    -- (2.55) ^ 2 * (x + 1) + (4 * x + 13) + 2 * (2.55) * (sqrt ((x + 1) * (4 * x + 13))) = 3 * x + 12
    -- The algebra earlier derived that this gives 3.55(x + 1) + 2 * sqrt(2.55 * (x + 1) * (4 * x + 13)) = 0
    -- The single solution is x = -1, which gives zero in each side of the equation.
    -- Now we need to complete the square to obtain h_eq to derive x = -1
    have h6 : x = -1 := by
      nlinarith [Real.sqrt_nonneg (3 * x + 12), Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg (4 * x + 13), sq_nonneg (2.55 * Real.sqrt (x + 1)), sq_nonneg (Real.sqrt (4 * x + 13) - 3), sq_nonneg (x + 1)]
    exact h6
  · -- Backward direction: if x = -1 then equation holds
    intro h_eq
    rw [h_eq]
    have h1 : Real.sqrt (-1 + 1 : ℝ) = 0 := by
      norm_num [Real.sqrt_eq_iff_sq_eq]
    have h2 : Real.sqrt (4 * (-1 : ℝ) + 13) = (3 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h3 : Real.sqrt (3 * (-1 : ℝ) + 12) = (3 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2, h3]
    all_goals norm_num
    all_goals norm_num [Real.sqrt_eq_iff_sq_eq]
    all_goals norm_num
    all_goals norm_num [Real.sqrt_eq_iff_sq_eq]
    all_goals norm_num
    all_goals norm_num [Real.sqrt_eq_iff_sq_eq]
    all_goals norm_num
    all_goals norm_num [Real.sqrt_eq_iff_sq_eq]
    all_goals norm_num