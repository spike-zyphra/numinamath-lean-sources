import Mathlib

theorem algebra_207584 (d : ℝ) (h : d = 4) (vbus vcycle : ℝ)
    (h1 : vbus > 0) (h2 : vcycle > 0) (h3 : vbus * 10 = vcycle * 15) (h4 : vbus * 20 = vcycle * 30 + d) :
    vbus = 40 := by
  rw [h] at h4
  linarith