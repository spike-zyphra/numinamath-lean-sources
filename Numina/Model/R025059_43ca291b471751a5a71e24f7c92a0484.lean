import Mathlib

theorem algebra_260352 {x y z : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (h1 : (x + y) / z = (y + z) / x) (h2 : (y + z) / x = (z + x) / y) :
    (x + y) * (y + z) * (z + x) / (x * y * z) = 8 ∨ (x + y) * (y + z) * (z + x) / (x * y * z) = -1 := by
  have eq1 : (x + y) * x = (y + z) * z := by
    field_simp [hx, hz] at h1
    nlinarith 
  have eq2 : (x - z) * (x + y + z) = 0 := by 
    nlinarith 
  have eq3 : (y + z) * y = (z + x) * x := by 
    field_simp [hx, hy] at h2
    nlinarith 
  have eq4 : (y - x) * (x + y + z) = 0 := by 
    nlinarith 
  by_cases h : x + y + z = 0 
  · -- x + y + z = 0 
    have eq5 : (x + y) * (y + z) * (z + x) = - (x * y * z) := by 
      have h3 : x + y + z = 0 := h 
      have h4 : x + y = - z := by linarith 
      have h5 : y + z = - x := by linarith 
      have h6 : z + x = - y := by linarith 
      rw [h4, h5, h6] 
      ring 
    have eq6 : (x + y) * (y + z) * (z + x) / (x * y * z) = -1 := by 
      rw [eq5] 
      field_simp [hx, hy, hz] 
      <;> nlinarith 
    right 
    exact eq6 
  · -- x + y + z ≠ 0 
    have h3 : x + y + z ≠ 0 := by 
      intro h4 
      apply h 
      linarith 
    have h4 : x - z = 0 := by 
      apply_fun (fun w => w / (x + y + z)) at eq2 
      field_simp [h3] at eq2 
      <;> linarith 
    have h5 : y - x = 0 := by 
      apply_fun (fun w => w / (x + y + z)) at eq4 
      field_simp [h3] at eq4 
      <;> linarith 
    have h6 : x = z := by linarith 
    have h7 : y = x := by linarith 
    have eq5 : (x + y) * (y + z) * (z + x) = 8 * (x * y * z) := by 
      rw [show y = x by linarith, show z = x by linarith] 
      ring_nf 
    have eq6 : (x + y) * (y + z) * (z + x) / (x * y * z) = 8 := by 
      rw [eq5] 
      field_simp [hx, hy, hz] 
      <;> nlinarith 
    left 
    exact eq6