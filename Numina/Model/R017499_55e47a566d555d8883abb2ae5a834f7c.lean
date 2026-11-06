import Mathlib

theorem other_171117 {F : ℝ} (hF : F = 150) (d : ℝ) (h : d > 0)
    (h1 : (d + 40) ^ 2 = F * d) :
    d = 170 := by
  rw [hF] at h1
  have h2 : (d - 35) ^ 2 + 375 = 0 := by
    nlinarith
  have h3 : (d - 35) ^ 2 ≥ 0 := by 
    apply sq_nonneg 
  nlinarith