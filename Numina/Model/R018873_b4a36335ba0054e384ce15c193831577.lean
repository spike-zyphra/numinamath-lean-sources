import Mathlib

theorem algebra_100926 {x a b : ℝ} (hx : x = a / b) (ha : a ≠ b) (hb : b ≠ 0) :
    (a + b) / (a - b) = (x + 1) / (x - 1) := by
  have h1 : a = x * b := by
    rw [hx]
    field_simp [hb]
    <;> nlinarith

  have h2 : a - b ≠ 0 := by
    intro h
    apply ha
    linarith

  have h3 : x - 1 ≠ 0 := by
    by_contra h4
    have h5 : x = 1 := by linarith
    have h7 : a = b := by
      have h8 : x = a / b := by linarith [hx]
      rw [h5] at h8
      have h9 : a / b = 1 := by linarith
      have h10 : a = b := by
        field_simp [hb] at h9 ⊢
        all_goals linarith
      assumption
    have h8 : a = b := h7
    contradiction

  have eq1 : (a + b) / (a - b) = (x + 1) / (x - 1) := by
    have h4 : a + b = b * (x + 1) := by
      rw [h1]
      ring
    have h5 : a - b = b * (x - 1) := by
      rw [h1]
      ring
    rw [h4, h5]
    have h6 : b * (x + 1) / (b * (x - 1)) = (x + 1) / (x - 1) := by
      have h7 : x - 1 ≠ 0 := h3
      have h8 : b ≠ 0 := hb
      field_simp [hb, h3]
      <;> nlinarith
      all_goals nlinarith
    exact h6
  exact eq1