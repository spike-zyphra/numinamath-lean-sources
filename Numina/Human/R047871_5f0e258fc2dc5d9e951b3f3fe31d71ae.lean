import Mathlib

/- 134. Three numbers are consecutive terms of some geometric progression. If 2 is added to the second number, they will form an arithmetic progression. If after that 16 is added to the third number, they will again form a geometric progression. Find these numbers. -/
theorem algebra_199289 {a r : ℤ} (hr : r ≠ 0) (h1 : a * r = a + 2) (h2 : a * r * (a + 2) = a * r + 16) :
    a = 1 ∧ r = 3 := by
  -- Restate the second condition for clarity
  have h3 : a * r * (a + 2) = a * r + 16 := h2
  -- Restate the first condition for clarity
  have h4 : a * r = a + 2 := h1
  -- Substitute the value of a*r into the second condition
  rw [h4] at h3
  -- Simplify the equation after substitution
  have h5 : (a + 2) * (a + 2) = (a + 2) + 16 := by nlinarith
  -- Convert to a standard form quadratic equation
  have h6 : a ^ 2 + 3 * a - 14 = 0 := by
    ring_nf at h5
    linarith
  -- Establish an upper bound for a
  have h7 : a ≤ 5 := by nlinarith
  -- Establish a lower bound for a
  have h8 : a ≥ -6 := by nlinarith
  -- Check all integer values in the range [-6, 5] to find the solution
  interval_cases a <;> omega
