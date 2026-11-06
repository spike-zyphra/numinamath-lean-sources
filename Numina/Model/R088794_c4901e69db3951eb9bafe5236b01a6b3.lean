import Mathlib

theorem algebra_243890 {x y : ℝ} (hy : y ≠ 0) (h : x / y = 2) : (x - y) / x = 1 / 2 := by
  have h1 : x = 2 * y := by
    field_simp [hy] at h
    linarith
  -- Prove x is not zero given y is not zero
  have hx : x ≠ 0 := by 
    intro h2
    have h3 : y = 0 := by
      linarith [h1, h2]
    contradiction
  have h2 : x - y = y := by
    linarith [h1]
  have h3 : y / x = 1 / 2 := by
    have h4 : x = 2 * y := h1
    field_simp [hx]
    linarith
  have : (x - y) / x = y / x := by
    rw [h2]
  rw [this, h3]