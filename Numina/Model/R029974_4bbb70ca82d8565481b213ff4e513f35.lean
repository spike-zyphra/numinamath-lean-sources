import Mathlib

open Real

theorem inequalities_182430 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y * z ≥ x * y + y * z + z * x) :
    Real.sqrt (x * y * z) ≥ Real.sqrt x + Real.sqrt y + Real.sqrt z := by
  have h1 : 0 < x * y * z := by
    apply mul_pos
    apply mul_pos
    all_goals
      positivity
  have h3 : Real.sqrt (x * y * z) ≥ Real.sqrt x + Real.sqrt y + Real.sqrt z := by
    have h4 : Real.sqrt (x * y * z) ≥ 0 := by positivity
    have h5 : Real.sqrt x + Real.sqrt y + Real.sqrt z ≥ 0 := by positivity
    have h6 : (Real.sqrt (x * y * z)) ^ 2 ≥ (Real.sqrt x + Real.sqrt y + Real.sqrt z) ^ 2 := by
      have h7 : (Real.sqrt (x * y * z)) ^ 2 = x * y * z := by
        rw [Real.sq_sqrt]
        positivity
      have h8 : (Real.sqrt x + Real.sqrt y + Real.sqrt z) ^ 2 = (Real.sqrt x) ^ 2 + (Real.sqrt y) ^ 2 + (Real.sqrt z) ^ 2 + 2 * (Real.sqrt x * Real.sqrt y + Real.sqrt y * Real.sqrt z + Real.sqrt z * Real.sqrt x) := by
        nlinarith
      have h9 : (Real.sqrt x) ^ 2 = x := by
        rw [Real.sq_sqrt]
        linarith [show 0 ≤ x by linarith]
      have h10 : (Real.sqrt y) ^ 2 = y := by
        rw [Real.sq_sqrt]
        linarith [show 0 ≤ y by linarith]
      have h11 : (Real.sqrt z) ^ 2 = z := by
        rw [Real.sq_sqrt]
        linarith [show 0 ≤ z by linarith]
      rw [h7, h8, h9, h10, h11]
      nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt y), sq_nonneg (Real.sqrt y - Real.sqrt z), sq_nonneg (Real.sqrt z - Real.sqrt x),
        Real.sqrt_nonneg (x * y * z), Real.sqrt_nonneg x, Real.sqrt_nonneg y, Real.sqrt_nonneg z,
        sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
        mul_nonneg (show 0 ≤ x by positivity) (show 0 ≤ y by positivity),
        mul_nonneg (show 0 ≤ y by positivity) (show 0 ≤ z by positivity),
        mul_nonneg (show 0 ≤ z by positivity) (show 0 ≤ x by positivity)]
    nlinarith [Real.sqrt_nonneg (x * y * z), Real.sqrt_nonneg x, Real.sqrt_nonneg y, Real.sqrt_nonneg z,
      Real.sq_sqrt (show (0 : ℝ) ≤ x * y * z by positivity),
      Real.sq_sqrt (show (0 : ℝ) ≤ x by positivity),
      Real.sq_sqrt (show (0 : ℝ) ≤ y by positivity),
      Real.sq_sqrt (show (0 : ℝ) ≤ z by positivity)]
  exact h3