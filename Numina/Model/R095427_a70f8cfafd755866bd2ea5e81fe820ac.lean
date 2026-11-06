import Mathlib

theorem algebra_128542 (d : ℝ) (h : d > 0) (h1 : 720 / (d - 720) = 400 / d) :
    d = 1760 := by
  have h2 : d - 720 ≠ 0 := by 
    by_contra h3
    have h4 : d = 720 := by linarith
    rw [h4] at h1
    norm_num at h1
  have h3 : d ≠ 0 := by linarith
  field_simp [(show d - 720 ≠ 0 by assumption), (show d ≠ 0 by assumption)] at h1
  nlinarith