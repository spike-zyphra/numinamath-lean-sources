import Mathlib

theorem algebra_22009 {z : ℂ} (h : z ≠ 0) (h1 : z + 1 / z = 1) : z ^ 3 = -1 := by
  have eq1 : z ^ 2 + 1 = z := by
    have h2 : z ≠ 0 := h
    have eq2 : z + 1 / z = 1 := h1
    have eq3 : z * (z + 1 / z) = z * 1 := by
      rw [eq2]
    have eq4 : z * (z + 1 / z) = z ^ 2 + 1 := by
      field_simp [h2]
      <;> ring
    rw [eq4] at eq3
    have eq5 : z * 1 = z := by ring
    rw [eq5] at eq3
    exact_mod_cast eq3
  have h3 : z ^ 2 = z - 1 := by
    have eq1 : z ^ 2 + 1 = z := eq1
    calc
      z ^ 2 = z ^ 2 + 1 - 1 := by ring_nf
      _ = z - 1 := by rw [eq1]; all_goals ring_nf
  calc
    z ^ 3 = z * z ^ 2 := by ring
    _ = z * (z - 1) := by rw [h3]
    _ = z ^ 2 - z := by ring_nf
    _ = (z - 1) - z := by rw [h3]
    _ = -1 := by ring_nf