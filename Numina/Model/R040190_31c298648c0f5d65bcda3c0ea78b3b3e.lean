import Mathlib

theorem algebra_325677 (x : ℝ) (hx : 1 ≤ x ∧ 3 ≤ 2 * x ∧ 5 ≤ 3 * x ∧ 7 ≤ 4 * x) :
    Real.sqrt (x - 1) + Real.sqrt (2 * x - 3) + Real.sqrt (3 * x - 5) +
    Real.sqrt (4 * x - 7) = 5 * x - 6 ↔ x = 2 := by
  constructor
  · -- Assume the equation, prove x = 2
    intro h_eq
    have h1 : 1 ≤ x := hx.1
    have h2 : 3 ≤ 2 * x := hx.2.1
    have h3 : 5 ≤ 3 * x := hx.2.2.1
    have h4 : 7 ≤ 4 * x := hx.2.2.2
    -- Show x = 2
    have h10' : (Real.sqrt (x - 1) ) ^2 = x - 1 := by
      apply Real.sq_sqrt
      linarith
    have h11' : (Real.sqrt (2 * x - 3)) ^2 = 2 * x - 3 := by
      apply Real.sq_sqrt
      linarith
    have h12' : (Real.sqrt (3 * x - 5)) ^2 = 3 * x - 5 := by
      apply Real.sq_sqrt
      linarith
    have h13' : (Real.sqrt (4 * x - 7)) ^2 = 4 * x - 7 := by
      apply Real.sq_sqrt
      linarith
    have h16 : x = 2 := by
      nlinarith [sq_nonneg (Real.sqrt (x - 1) - 1), sq_nonneg (Real.sqrt (2 * x - 3) - 1), sq_nonneg (Real.sqrt (3 * x - 5) - 1), sq_nonneg (Real.sqrt (4 * x - 7) - 1), 
          Real.sqrt_nonneg (x - 1), Real.sqrt_nonneg (2 * x - 3), 
          Real.sqrt_nonneg (3 * x - 5), Real.sqrt_nonneg (4 * x - 7)
          ]
    exact_mod_cast h16
  · -- Backward: if x = 2, prove the equation
    intro h_eq
    rw [h_eq]
    have h1 : Real.sqrt (2 - 1 : ℝ) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : Real.sqrt (2 * (2 : ℝ) - 3) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h3 : Real.sqrt (3 * (2 : ℝ) - 5) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h4 : Real.sqrt (4 * (2 : ℝ) - 7) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2, h3, h4]
    all_goals norm_num