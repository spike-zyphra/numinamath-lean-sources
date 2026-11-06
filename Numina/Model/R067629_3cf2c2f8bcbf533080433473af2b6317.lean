import Mathlib

theorem algebra_93761 (d v : ℝ) (h₀ : d > 0) (h₁ : v > 0)
    (h₂ : d / v = 60) (h₃ : d / (v + w) = 24) :
    d / w = 40 := by 
  have h4 : d = 60 * v := by
    have h5 : v ≠ 0 := by linarith
    field_simp [h5] at h₂
    linarith
  
  have h5 : v + w ≠ 0 := by
    by_contra h 
    have h6 : d / (v + w) = 0 := by
      rw [h]
      norm_num
    linarith [h₃, h6]

  have h6 : d = 24 * (v + w) := by
    have h7 : v + w ≠ 0 := h5
    field_simp [h7] at h₃
    linarith
  
  rw [h4] at h6
  have hw : w = (3 / 2) * v := by
    nlinarith
  
  have hw2 : w ≠ 0 := by 
    by_contra h 
    rw [h] at hw
    nlinarith [h₁]
  
  have final_eq : d / w = 40 := by 
    rw [show d = 60 * v by linarith [h4], show w = (3 / 2) * v by linarith [hw]]
    have hv : v ≠ 0 := by linarith
    field_simp [hv]
    all_goals nlinarith
  
  linarith [final_eq]