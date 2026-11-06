import Mathlib

/- The third and fourth terms of a geometric sequence are 12 and 16, respectively. What is the first term of the sequence? -/
theorem algebra_16036 {a r : ℚ} (hr : r ≠ 0) (h3 : a * r^2 = 12) (h4 : a * r^3 = 16) :
    a = 27 / 4 := by 
  have h5 : r = 16 / 12 := by
    apply Eq.symm
    nlinarith
  rw [h5] at h3
  nlinarith