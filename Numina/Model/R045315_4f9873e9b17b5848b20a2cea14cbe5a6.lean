import Mathlib

theorem algebra_195431 {x y z : ℝ} (h : x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0)
    (h1 : (x + y - z) / z = (x - y + z) / y) (h2 : (x - y + z) / y = (-x + y + z) / x) :
    ((x + y) * (y + z) * (z + x)) / (x * y * z) = -1 ∨ ((x + y) * (y + z) * (z + x)) / (x * y * z) = 8 := by
  rcases h with ⟨hx, hy, hz⟩
  have eq1 : y * (x + y - z) = z * (x - y + z) := by
    have h1' : (x + y - z) / z = (x - y + z) / y := h1
    field_simp [hz, hy] at h1' ⊢
    linarith
  have eq2 : x * (x - y + z) = y * (-x + y + z) := by
    have h2' : (x - y + z) / y = (-x + y + z) / x := h2
    field_simp [hy, hx] at h2' ⊢
    linarith
  have eq3 : (y - z) * (x + y + z) = 0 := by
    nlinarith
  have eq4 : (x - y) * (x + y + z) = 0 := by
    nlinarith
  by_cases h3 : x + y + z = 0
  · -- Case where x + y + z = 0
    have eq5 : (x + y) * (y + z) * (z + x) = - (x * y * z) := by
      have h4 : x + y = -z := by linarith
      have h5 : y + z = -x := by linarith
      have h6 : z + x = -y := by linarith
      rw [h4, h5, h6]
      ring
    have eq6 : ((x + y) * (y + z) * (z + x)) / (x * y * z) = -1 := by
      rw [eq5]
      field_simp [hx, hy, hz]
    left
    linarith
  · -- Case where x + y + z ≠ 0
    have h4 : y - z = 0 := by
      apply_fun (fun w => w / (x + y + z)) at eq3
      field_simp [h3] at eq3 ⊢
      linarith
    have h5 : x - y = 0 := by
      apply_fun (fun w => w / (x + y + z)) at eq4
      field_simp [h3] at eq4 ⊢
      linarith
    have h6 : y = z := by linarith
    have h7 : x = y := by linarith
    have eq7 : (x + y) * (y + z) * (z + x) = 8 * (x * y * z) := by
      rw [show y = x by linarith [h7], show z = x by linarith [h7, h6]]
      ring_nf
    have eq8 : ((x + y) * (y + z) * (z + x)) / (x * y * z) = 8 := by
      rw [eq7]
      field_simp [hx, hy, hz]
    right
    linarith