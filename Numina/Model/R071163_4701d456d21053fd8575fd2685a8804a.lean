import Mathlib

theorem algebra_176548 {x : ℝ} (hx : x > 0) (h : x^2 + 1/x^2 = 7) :
    ∃ n : ℤ, x^5 + 1/x^5 = n ∧ n = 123 := by

  have h1 : x + 1 / x = 3 := by
    have h2 : (x + 1 / x) ^ 2 = 9 := by
      have h3 : (x + 1 / x) ^ 2 = x ^ 2 + 1 / x ^ 2 + 2 := by
        field_simp
        ring
      rw [h3, h]
      norm_num
    have h4 : x + 1 / x > 0 := by
      have hx1 : x > 0 := hx
      have hx2 : 1 / x > 0 := by
        apply div_pos
        norm_num
        exact hx
      linarith
    have h5 : x + 1 / x = 3 := by nlinarith
    exact h5

  have h2 : x ^ 3 + 1 / x ^ 3 = 18 := by
    have h3 : (x + 1 / x) ^ 3 = x ^ 3 + 1 / x ^ 3 + 3 * (x + 1 / x) := by
      field_simp
      ring
    rw [h1] at h3
    nlinarith

  have h4 : x ^ 4 + 1 / x ^ 4 = 47 := by
    have h5 : (x ^ 2 + 1 / x ^ 2) ^ 2 = x ^ 4 + 1 / x ^ 4 + 2 := by
      field_simp
      ring
    rw [h] at h5
    nlinarith

  have h5 : x ^ 5 + 1 / x ^ 5 = (123 : ℝ) := by
    have h6 : (x + 1 / x) * (x ^ 4 + 1 / x ^ 4) = x ^ 5 + 1 / x ^ 5 + (x ^ 3 + 1 / x ^ 3) := by
      field_simp
      ring
    rw [h1, h4, h2] at h6
    nlinarith

  use 123
  constructor
  · -- Show that x^5 + 1/x^5 = (123 : ℝ)
    linarith [h5]
  · -- Trivial equality
    rfl