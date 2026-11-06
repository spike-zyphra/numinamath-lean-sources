import Mathlib

theorem algebra_15605 {m : ℝ} 
    (hm₁ : 0 < m - 2) (hm₂ : 0 < 2 * m + 7) 
    (h : (2 * m + 7) * (m - 2) = 51) : m = 5 := by 
  have h1 : 2 * m ^ 2 + 3 * m - 65 = 0 := by 
    ring_nf at h 
    linarith 
  have : (2 * m + 13) * (m - 5) = 0 := by linarith [h1]
  cases' mul_eq_zero.mp this <;> linarith
  