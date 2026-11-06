import Mathlib

theorem algebra_304194 {a b c : ℝ} (ha : a ≠ 0) (h : ∀ x, a * (1 - x) ^ 2 + b * (1 - x) + c = a * (1 + x) ^ 2 + b * (1 + x) + c)
    (h' : a * 2 ^ 2 + b * 2 + c = 0) : (a * (-1) ^ 2 + b * (-1) + c) / (a * (1) ^ 2 + b * (1) + c) = -3 := by
  have eq1 := h 1
  have eq2 := h 2
  have eq3 : 4 * a + 2 * b = 0 := by
    simp at eq1
    linarith
  have eq4 : 8 * a + 4 * b = 0 := by
    simp at eq2
    linarith
  have eq5 : b = -2 * a := by
    linarith [eq3, eq4]
  have eq6 : c = 0 := by
    rw [show b = -2 * a by linarith [eq5]] at h'
    linarith
  have h1 : a * (-1) ^ 2 + b * (-1) + c = 3 * a := by
    rw [show b = -2 * a by linarith [eq5], show c = 0 by linarith [eq6]]
    ring
  have h2 : a * (1) ^ 2 + b * (1) + c = -a := by
    rw [show b = -2 * a by linarith [eq5], show c = 0 by linarith [eq6]]
    ring
  have h3 : (a * (-1) ^ 2 + b * (-1) + c) / (a * (1) ^ 2 + b * (1) + c) = -3 := by
    rw [h1, h2]
    have h4 : a ≠ 0 := ha
    field_simp [h4]
    <;> ring
  exact h3