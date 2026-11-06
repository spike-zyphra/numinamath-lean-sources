import Mathlib

theorem algebra_295042 (x y z : ℝ) (hx : 0 ≤ x) (hy : 1 ≤ y) (hz : 2 ≤ z)
    (h : Real.sqrt x + Real.sqrt (y - 1) + Real.sqrt (z - 2) = (x + y + z) / 2) :
    x = 1 ∧ y = 2 ∧ z = 3 := by
  have h1 : 0 ≤ Real.sqrt x := by positivity
  have h2 : 0 ≤ Real.sqrt (y - 1) := by positivity
  have h3 : 0 ≤ Real.sqrt (z - 2) := by positivity

  have h4 : 2 * Real.sqrt x ≤ x + 1 := by
    nlinarith [Real.sqrt_nonneg x, Real.sq_sqrt (show 0 ≤ x by linarith),
      sq_nonneg (Real.sqrt x - 1)]
  have h5 : 2 * Real.sqrt (y - 1) ≤ (y - 1) + 1 := by
    nlinarith [Real.sqrt_nonneg (y - 1), Real.sq_sqrt (show 0 ≤ y - 1 by linarith),
      sq_nonneg (Real.sqrt (y - 1) - 1)]
  have h6 : 2 * Real.sqrt (z - 2) ≤ (z - 2) + 1 := by
    nlinarith [Real.sqrt_nonneg (z - 2), Real.sq_sqrt (show 0 ≤ z - 2 by linarith),
      sq_nonneg (Real.sqrt (z - 2) - 1)]

  have h7 : x = 1 := by
    nlinarith [show Real.sqrt x + Real.sqrt (y - 1) + Real.sqrt (z - 2) = (x + y + z) / 2 from h,
      sq_nonneg (Real.sqrt x - 1), sq_nonneg (Real.sqrt (y - 1) - 1), sq_nonneg (Real.sqrt (z - 2) - 1),
      Real.sqrt_nonneg x, Real.sqrt_nonneg (y - 1), Real.sqrt_nonneg (z - 2),
      Real.sq_sqrt (show 0 ≤ x by linarith), Real.sq_sqrt (show 0 ≤ y - 1 by linarith), Real.sq_sqrt (show 0 ≤ z - 2 by linarith)]
  
  have h8 : y = 2 := by
    nlinarith [show Real.sqrt x + Real.sqrt (y - 1) + Real.sqrt (z - 2) = (x + y + z) / 2 from h,
      sq_nonneg (Real.sqrt x - 1), sq_nonneg (Real.sqrt (y - 1) - 1), sq_nonneg (Real.sqrt (z - 2) - 1),
      Real.sqrt_nonneg x, Real.sqrt_nonneg (y - 1), Real.sqrt_nonneg (z - 2),
      Real.sq_sqrt (show 0 ≤ x by linarith), Real.sq_sqrt (show 0 ≤ y - 1 by linarith), Real.sq_sqrt (show 0 ≤ z - 2 by linarith)]
  
  have h9 : z = 3 := by
    nlinarith [show Real.sqrt x + Real.sqrt (y - 1) + Real.sqrt (z - 2) = (x + y + z) / 2 from h,
      sq_nonneg (Real.sqrt x - 1), sq_nonneg (Real.sqrt (y - 1) - 1), sq_nonneg (Real.sqrt (z - 2) - 1),
      Real.sqrt_nonneg x, Real.sqrt_nonneg (y - 1), Real.sqrt_nonneg (z - 2),
      Real.sq_sqrt (show 0 ≤ x by linarith), Real.sq_sqrt (show 0 ≤ y - 1 by linarith), Real.sq_sqrt (show 0 ≤ z - 2 by linarith)]
  
  constructor
  · exact h7
  constructor
  · exact h8
  · exact h9