import Mathlib

theorem algebra_296865 {x y : ℕ} (hx : x > 0) (hy : y > 0)
    (h1 : x * y + x + y = 23) (h2 : x^2 * y + x * y^2 = 120) :
    x^2 + y^2 = 34 := by
  have eq3 : x^2 * y + x * y^2 = (x * y) * (x + y) := by 
    ring
  rw [eq3] at h2
  have h3 : (x + 1) * (y + 1) = 24 := by 
    nlinarith
  have h4 : x ≤ 11 := by
    by_contra h
    push_neg at h
    have h5 : (x + 1) * (y + 1) = 24 := h3
    have h6 : y + 1 ≤ 2 := by
      nlinarith
    have h7 : y ≤ 1 := by 
      omega
    have h8 : y = 1 := by 
      omega
    rw [show y = 1 by linarith] at h1 h2 h3
    nlinarith
    all_goals
      omega
  have h5 : y ≤ 11 := by 
    by_contra h
    push_neg at h
    have h5 : (x + 1) * (y + 1) = 24 := h3
    have h6 : x + 1 ≤ 2 := by
      nlinarith
    have h7 : x ≤ 1 := by
      omega
    have h8 : x = 1 := by
      omega
    rw [show x = 1 by linarith] at h1 h2 h3
    nlinarith
  interval_cases x <;> interval_cases y <;> omega