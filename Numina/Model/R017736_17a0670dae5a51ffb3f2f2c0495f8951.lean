import Mathlib

theorem algebra_6537 {a b x : ℝ} (h : a ≠ b) (hb : b ≠ 0) (hx : x = a / b) :
    (a + b) / (a - b) = (x + 1) / (x - 1) := by
  have h1 : a = x * b := by
    rw [hx]
    field_simp [hb]
  have h2 : a + b = b * (x + 1) := by
    rw [h1]
    ring
  have h3 : a - b = b * (x - 1) := by
    rw [h1]
    ring
  rw [h2, h3]
  have hx1 : x - 1 ≠ 0 := by
    by_contra h4
    have h5 : x = 1 := by linarith
    have h6 : a / b = 1 := by
      rw [show a / b = x by linarith [hx]]
      rw [h5]
    have h7 : a = b := by
      have h8 : a / b = 1 := h6
      field_simp [hb] at h8 ⊢
      all_goals linarith
    have h8 : a = b := h7
    contradiction
  have h5 : b ≠ 0 := hb
  field_simp [hb, hx1]
  <;> ring