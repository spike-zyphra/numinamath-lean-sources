import Mathlib

theorem algebra_239392 (v : ℝ) (h : v > 0) (h' : 60 / (v + 10) = 60 / v - 12 / 60) :
    v = 50 := by
  
  have h1 : v + 10 ≠ 0 := by
    by_contra h2
    have h3 : v = -10 := by linarith
    linarith

  have h2 : v ≠ 0 := by linarith
  
  field_simp [h1, h2] at h'

  have h3 : v^2 + 10 * v - 3000 = 0 := by 
    nlinarith
  
  have h4 : (v - 50) * (v + 60) = 0 := by 
    nlinarith [h3]

  cases' (mul_eq_zero.mp h4) with h5 h6

  · -- Case $v - 50 = 0$, so $v = 50$
    linarith

  · -- Case $v + 60 = 0$, so $v = -60$, which contradicts $v > 0$
    linarith