import Mathlib

theorem algebra_194199 (x y : ℝ) (hx : x > 0) (hy : y > 0)
    (h1 : x = y - 15) (h2 : 18 / y + 6 / x = 0.6) :
    y = 45 := by
  have h3 : y > 15 := by 
    have hx2 : x > 0 := hx
    rw [h1] at hx2
    linarith
  have eq1 : 18 / y + 6 / x = 0.6 := h2
  rw [h1] at eq1
  have eq2 : y ≠ 0 := by nlinarith
  have eq3 : (y - 15) ≠ 0 := by
    nlinarith
  field_simp [eq2, eq3] at eq1
  ring_nf at eq1 
  have h4 : y ^ 2 - 55 * y + 450 = 0 := by nlinarith
  have h5 : (y - 45) * (y - 10) = 0 := by
    nlinarith [h4]
  cases' (mul_eq_zero.mp h5) with h6 h7
  · -- Case where y = 45
    linarith
  · -- Case where y = 10, which is impossible
    have h8 : y = 10 := by linarith
    linarith