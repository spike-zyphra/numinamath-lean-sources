import Mathlib

theorem algebra_20531 {a d : ℤ} (h : a > 0) (h' : d > 0) (h'' : a * (a + 2 * d) = 5) :
    a + 3 * d = 7 := by
  have h1 : a ≤ 5 := by
    nlinarith
  have h2 : a ≥ 1 := by
    linarith
  have h3 : a = 1 := by
    interval_cases a <;> 
    omega
  have h4 : d = 2 := by
    rw [h3] at h''
    nlinarith
  rw [h3, h4]
  all_goals omega