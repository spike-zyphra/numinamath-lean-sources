import Mathlib

theorem algebra_214804 {x y z : ℝ} (h1 : x + y - z = 2) (h2 : x^2 + y^2 - z^2 = -4) (h3 : x^3 + y^3 - z^3 = 8) :
    x = 0 ∧ y = 0 ∧ z = -2 := by
  have h4 : z = x + y - 2 := by linarith
  rw [h4] at h2
  have h5 : 2 * (x + y) = x * y := by
    nlinarith
  rw [h4] at h3
  have h7 : (x + y) * ((x + y) - 2) = 0 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 2), sq_nonneg (x + y), sq_nonneg (x * y)]
  have h8 : x + y = 0 := by
    nlinarith
  have h9 : x * y = 0 := by
    nlinarith [h8, h5]
  have hx1 : x = 0 := by
    cases' (mul_eq_zero.mp h9) with hx hy
    · -- Case where $h9 = hx : x = 0$
      linarith
    · -- Case where $h9 = hy : y = 0$
      have : y = 0 := by linarith
      have : x = 0 := by linarith [h8, this]
      linarith
  have hy2 : y = 0 := by
    linarith [h8, hx1]
  have hz : z = -2 := by
    rw [hx1, hy2] at h4
    linarith
  exact ⟨hx1, hy2, hz⟩