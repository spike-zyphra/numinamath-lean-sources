import Mathlib

theorem algebra_207597 (x : ℝ) (hx : x ≠ 0) (h : (1 / 2) * x * (1 / 3) = (1 / 4) * x * (1 / 5)) :
    (15 / x) * (1 / 5) = 2 := by
  have h1 : x ≠ 0 := hx
  have h2 : (1 / 6) * x = (1 / 20) * x := by
    linarith
  have h3 : (1 / 6 : ℝ) = (1 / 20 : ℝ) := by
    apply (mul_left_inj' h1).mp
    linarith
  norm_num at h3 
  all_goals
    nlinarith