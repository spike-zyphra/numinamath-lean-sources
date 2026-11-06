import Mathlib

theorem algebra_176185 {x : ℝ} (hx : x = 1 / (1 + x)) (hx' : x ≠ -1) : x - 1 / x = -1 := by 
  have h1 : 1 + x ≠ 0 := by 
    intro h
    apply hx'
    linarith 
  have h2 : x * (1 + x) = 1 := by
    have h3 : 1 + x ≠ 0 := h1 
    field_simp [h3] at hx ⊢ 
    nlinarith
  have h3 : x ≠ 0 := by 
    by_contra h
    rw [h] at h2
    norm_num at h2 
  have h4 : 1 / x = 1 + x := by 
    have h5 : x ≠ 0 := h3 
    field_simp [h5] at *
    nlinarith 
  rw [h4]
  linarith