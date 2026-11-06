import Mathlib

theorem algebra_225657 {x y : ℝ} (hxy : x ≠ y) (h1 : x + 4 = (y - 2) ^ 2) (h2 : y + 4 = (x - 2) ^ 2) :
    x ^ 2 + y ^ 2 = 15 := by
  have h3 : x + y = 3 := by
    have h4 : x - y = (y - 2) ^ 2 - (x - 2) ^ 2 := by
      linarith [h1, h2]
    have h5 : (y - 2) ^ 2 - (x - 2) ^ 2 = - (x - y) * (x + y - 4) := by
      ring_nf
    rw [h5] at h4
    have h6 : (x - y) * (x + y - 3) = 0 := by
      linarith
    cases' (mul_eq_zero.mp h6) with h7 h8
    · 
      exfalso
      have h9 : x = y := by linarith
      exact hxy (by linarith)
    · 
      linarith
  nlinarith [h1, h2, h3]