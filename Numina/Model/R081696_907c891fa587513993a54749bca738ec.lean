import Mathlib

theorem algebra_171390 (m1 m2 : ℝ) (h : m2 = 20) (h1 : m1 / 3 = m2 / 5) (h2 : 7 * m1 = 5 * m2) :
    m1 = 5.2 := by 
  rw [h] at h1 h2
  linarith