import Mathlib

theorem algebra_16036 {a r : ℚ} (hr : r ≠ 0) (h3 : a * r^2 = 12) (h4 : a * r^3 = 16) :
    a = 27 / 4 := by 
  have hr_eq : r = 4 / 3 := by 
    have h5 : r ≠ 0 := hr
    have h6 : a * r^3 - a * r^2 = 16 - 12 := by linarith 
    have h7 : a * r^2 * (r - 1) = 4 := by 
      linarith 
    rw [show a * r^2 = 12 by linarith] at h7 
    linarith [h7]
  rw [hr_eq] at h3 
  nlinarith