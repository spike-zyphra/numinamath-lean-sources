import Mathlib

theorem algebra_1732 {x : ℝ} (hx : x ≠ 2) (h : x + 1 / (x - 2) = 4 + 1 / 2) : x = 4 ∨ x = 5 / 2 := by
  have h1 : x - 2 ≠ 0 := by
    intro h2
    apply hx
    linarith
  have eq1 : x + 1 / (x - 2) = 9 / 2 := by
    have h2 : x + 1 / (x - 2) = 4 + 1 / 2 := h
    norm_num at h2 ⊢
    linarith
  have eq2 : x * (x - 2) + 1 = (9 / 2) * (x - 2) := by
    have eq3 : x + 1 / (x - 2) = 9 / 2 := eq1
    have eq4 : (x + 1 / (x - 2)) * (x - 2) = (9 / 2) * (x - 2) := by
      rw [eq3]
    have eq5 : (x + 1 / (x - 2)) * (x - 2) = x * (x - 2) + 1 := by
      field_simp [h1]
      <;> ring
    rw [eq5] at eq4
    linarith
  have quad_eq : 2 * x^2 - 13 * x + 20 = 0 := by
    nlinarith [eq2]
  have quad_sol : (x - 4) * (x - 5 / 2) = 0 := by
    nlinarith [quad_eq]
  cases' (mul_eq_zero.mp quad_sol) with h4 h5
  · -- Case where x - 4 = 0, so x = 4
    left
    linarith
  · -- Case where x - 5/2 = 0, so x = 5/2
    right
    linarith