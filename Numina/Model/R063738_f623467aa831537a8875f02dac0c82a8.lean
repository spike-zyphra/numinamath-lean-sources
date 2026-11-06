import Mathlib

theorem algebra_289965 (x : ℝ) (hx : x ≠ 0) : 8 / x + 6 = 8 ↔ x = 4 := by
  constructor
  · -- Forward direction: Assume 8 / x + 6 = 8, prove x = 4
    intro h
    have h1 : 8 / x = 2 := by
      linarith
    have h2 : x ≠ 0 := hx
    have h3 : 8 = 2 * x := by
      field_simp [h2] at h1 ⊢
      linarith
    have h4 : x = 4 := by
      linarith
    exact h4
  · -- Reverse direction: Assume x = 4, prove 8 / x + 6 = 8
    intro h
    rw [h]
    norm_num