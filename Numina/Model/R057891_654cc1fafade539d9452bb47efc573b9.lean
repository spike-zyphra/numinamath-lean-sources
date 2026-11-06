import Mathlib

theorem algebra_141139 (t : ℝ) (ht : t > 0) (h : 36 / (t + 2) = 36 / t - 0.20) :
    t = 18 := by
  have h1 : t + 2 ≠ 0 := by 
    linarith
  have h2 : t ≠ 0 := by 
    linarith
  have eq1 : 36 / (t + 2) = 36 / t - (0.20 : ℝ) := by 
    linarith
  have eq2 : 36 * t = 36 * (t + 2) - (0.20 : ℝ) * (t * (t + 2)) := by
    have h3 : (t : ℝ) ≠ 0 := by linarith
    have h4 : (t + 2 : ℝ) ≠ 0 := by linarith
    field_simp [h3, h4] at eq1 ⊢
    nlinarith
  ring_nf at eq2 ⊢
  have h_eq : t^2 + 2 * t - 360 = 0 := by nlinarith
  have h3 : (t - 18) * (t + 20) = 0 := by 
    nlinarith [h_eq]
  cases' (mul_eq_zero.mp h3) with h4 h5
  · linarith
  · linarith