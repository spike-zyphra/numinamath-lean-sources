import Mathlib

theorem algebra_193591 {x y z : ℝ} (h1 : x = 1.4 * y) (h2 : x / z = 14 / 11)
    (h3 : z - y = 0.125 * (x + y) - 40) :
    x = 280 ∧ y = 200 ∧ z = 220 := by 
  have h4 : z ≠ 0 := by
    by_contra h
    rw [h] at h2
    norm_num at h2
    all_goals linarith

  have h5 : 11 * x - 14 * z = 0 := by 
    have h6 : x / z = 14 / 11 := h2
    field_simp [h4] at h6 ⊢
    linarith
  
  have h8 : z = (1.1) * y := by 
    rw [show x = (1.4) * y by linarith] at h5 
    ring_nf at h5
    linarith
  
  have h9 : y = 200 := by 
    rw [show z = (1.1) * y by linarith] at h3
    rw [show x = 1.4 * y by linarith] at h3
    ring_nf at h3
    linarith
  
  have h10 : x = 280 := by 
    rw [show y = 200 by linarith] at h1 
    linarith
  
  have h11 : z = 220 := by 
    rw [show y = 200 by linarith] at h8 
    linarith
  
  exact ⟨h10, h9, h11⟩