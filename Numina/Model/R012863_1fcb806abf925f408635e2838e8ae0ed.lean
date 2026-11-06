import Mathlib

theorem algebra_196752 {x : ℝ} (hx : x ≥ -1 / 4) (n : ℕ) (hn : n > 1) :
    x + Real.sqrt (x + 1 / 2 + Real.sqrt (x + 1 / 4)) = n ^ 2 ↔ x = n ^ 2 - n := by
  constructor
  · -- (→) If x + √(x + 1/2 + √(x + 1/4)) = n² then x = n²-n
    intro h_eq
    have h1 : n ≥ 2 := by
      omega
    have h2 : (n : ℝ) ≥ 2 := by
      exact_mod_cast h1
    have h3 : Real.sqrt (x + 1 / 4) ≥ 0 := Real.sqrt_nonneg (x + 1 / 4)
    have h4 : Real.sqrt (x + 1 / 2 + Real.sqrt (x + 1 / 4)) ≥ 0 := Real.sqrt_nonneg (x + 1 / 2 + Real.sqrt (x + 1 / 4))
    have h6 : (Real.sqrt (x + 1 / 4)) ^ 2 = x + 1 / 4 := Real.sq_sqrt (by linarith)
    have h7 : (Real.sqrt (x + 1 / 2 + Real.sqrt (x + 1 / 4))) ^ 2 = x + 1 / 2 + Real.sqrt (x + 1 / 4) := by
      rw [Real.sq_sqrt]
      nlinarith [Real.sqrt_nonneg (x + 1 / 4)]
    have h8 : (n : ℝ) ≥ 2 := h2
    have h9 : n > 1 := by
      omega
    have h10 : x = (n : ℝ) ^ 2 - (n : ℝ) := by
      nlinarith [Real.sqrt_nonneg (x + 1 / 4), Real.sqrt_nonneg (x + 1 / 2 + Real.sqrt (x + 1 / 4)), Real.sq_sqrt (show 0 ≤ (x + 1 / 4 : ℝ) by nlinarith), Real.sq_sqrt (show 0 ≤ (x + 1 / 2 + Real.sqrt (x + 1 / 4)) by nlinarith), sq_nonneg ((n : ℝ) - 1), sq_nonneg ((Real.sqrt (x + 1 / 4)) - ((n : ℝ) - 1 / 2)), sq_nonneg ((Real.sqrt (x + 1 / 2 + Real.sqrt (x + 1 / 4))) - (n : ℝ)), sq_nonneg ((x) - ((n : ℝ) ^ 2 - (n : ℝ)))]
    exact_mod_cast h10
  · -- (←) If x = n²-n, then it satisfies the equation.
    intro h_eq
    have h1 : n ≥ 2 := by
      omega
    have h2 : (n : ℝ) ≥ 2 := by
      exact_mod_cast h1
    have h3 : x = (n : ℝ) ^ 2 - (n : ℝ) := by
      exact_mod_cast h_eq
    have h4 : x + 1 / 4 = ((n : ℝ) - 1 / 2) ^ 2 := by
      nlinarith
    have h5 : Real.sqrt (x + 1 / 4) = (n : ℝ) - 1 / 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith
    have h6 : Real.sqrt (x + 1 / 4) = (n : ℝ) - 1 / 2 := h5
    have h7 : x + 1 / 2 + Real.sqrt (x + 1 / 4) = (n : ℝ) ^ 2 := by
      nlinarith [h4, h5, Real.sqrt_nonneg (x + 1 / 4), Real.sqrt_nonneg (x + 1 / 4)]
    have h8 : Real.sqrt (x + 1 / 2 + Real.sqrt (x + 1 / 4)) = (n : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> nlinarith
    nlinarith [h5, h8, Real.sqrt_nonneg (x + 1 / 4), Real.sqrt_nonneg (x + 1 / 4)]