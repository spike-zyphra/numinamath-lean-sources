import Mathlib

theorem algebra_145107 {a : ℝ} (ha : a ≠ 0) (h : ((1 - (1 - a⁻¹)⁻¹)⁻¹ = 3)) :
    a = -2 := by
  have h1 : a ≠ 1 := by 
    by_contra h1
    rw [h1] at h
    norm_num [h1] at h
  have h2 : a - 1 ≠ 0 := by
    intro h'
    apply h1
    linarith
  have eq1 : (1 - (1 - a⁻¹)⁻¹)⁻¹ = 1 - a := by
    have h3 : a ≠ 0 := ha
    have h4 : a - 1 ≠ 0 := h2
    have eq2 : (1 - a⁻¹) = (a - 1) / a := by
      field_simp [h3]
    have eq3 : (1 - a⁻¹)⁻¹ = a / (a - 1) := by
      rw [eq2]
      field_simp [(show a ≠ 0 by exact h3), (show a - 1 ≠ 0 by exact h4)]
    have eq4 : (1 - (1 - a⁻¹)⁻¹) = -1 / (a - 1) := by
      rw [eq3]
      field_simp [(show a ≠ 0 by exact h3), (show a - 1 ≠ 0 by exact h4)]
      <;> ring
    have eq5 : (1 - (1 - a⁻¹)⁻¹)⁻¹ = 1 - a := by
      rw [eq4]
      field_simp [(show a ≠ 0 by exact h3), (show a - 1 ≠ 0 by exact h4)]
      <;> ring
    exact eq5
  rw [eq1] at h
  linarith