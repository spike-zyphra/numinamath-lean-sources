import Mathlib

theorem algebra_3829 (x : ℝ) (hx : x > 0) (h : (72 * 4 + 90 * x) / (4 + x) ≥ 85) :
    x ≥ 10.4 := by
  have h1 : 4 + x > 0 := by linarith
  have h2 : 72 * 4 + 90 * x ≥ 85 * (4 + x) := by
    apply (le_div_iff₀ h1).mp at h
    linarith
  have h5 : 5 * x ≥ 52 := by 
    linarith [h2]
  have h6 : x ≥ (52 : ℝ) / 5 := by 
    linarith [h5]
  have h7 : (52 : ℝ) / 5 = 10.4 := by norm_num 
  linarith [h6, h7]