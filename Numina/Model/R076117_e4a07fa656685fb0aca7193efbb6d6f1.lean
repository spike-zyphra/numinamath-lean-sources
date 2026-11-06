import Mathlib

theorem algebra_279175 (x : ℝ) (hx : x ∈ Set.Icc 0 1) (h : (1 / 3) * 0.55 + (2 / 3) * x = 3 / 4) :
    x = 0.85 := by 
  have hx1 : x ≥ 0 := hx.1
  have hx2 : x ≤ 1 := hx.2
  norm_num at h 
  linarith