import Mathlib

theorem algebra_267510 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : (x * 0.8) / (y * 1.25) = (1 - z) * x / y) :
    z = 0.36 := by
  have eq1 : (x * 0.8) / (y * 1.25) = (1 - z) * x / y := h
  have eq2 : x * 0.8 = (1 - z) * x * 1.25 := by
    have h1' : (x * 0.8) / (y * 1.25) = (1 - z) * x / y := h 
    have h3 : (x * 0.8 : ℝ) = ( (1 - z) * x / y ) * (y * 1.25) := by 
      have h2a : ( (x * 0.8) / (y * 1.25) ) * (y * 1.25) = ( (1 - z) * x / y ) * (y * 1.25) := by 
        rw [h1']
      have h4 : ( (x * 0.8) / (y * 1.25) ) * (y * 1.25) = x * 0.8 := by 
        field_simp [hy]
      rw [h4] at h2a 
      linarith 
    have h5 : ( (1 - z) * x / y ) * (y * 1.25) = (1 - z) * x * 1.25 := by 
      field_simp [hy]
      <;> ring 
    rw [h5] at h3 
    linarith 
  have eq3 : z = 1 - (0.8 / 1.25 : ℝ) := by 
    have eq4' : x * 0.8 = (1 - z) * x * 1.25 := eq2 
    have hx1 : x ≠ 0 := hx 
    apply (mul_left_inj' hx1).mp 
    linarith 
  rw [eq3]
  norm_num