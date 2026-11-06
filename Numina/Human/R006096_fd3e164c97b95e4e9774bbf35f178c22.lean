import Mathlib

theorem algebra_764 {pa b : ℤ} (hpa : pa = b - 20) (hpa' : 2 * pa = 180) :
    b = 110 := by
  rw [hpa] at hpa'
  linarith