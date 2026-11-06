import Mathlib

theorem algebra_128765 {x y : ℝ} (h₀ : x + y = 1) (h₁ : x^3 + y^3 = 19) :
    (x, y) = (3, -2) ∨ (x, y) = (-2, 3) := by
  have h2 : x * y = -6 := by
    have h : x^3 + y^3 = (x + y) ^ 3 - 3 * (x * y) * (x + y) := by
      ring
    rw [h₀] at h
    rw [h₁] at h
    nlinarith
  have h3 : x^2 - x - 6 = 0 := by
    have h_eq1 : x + y = 1 := h₀
    have h_eq2 : x * y = -6 := h2
    have hy : y = 1 - x := by linarith
    rw [hy] at h_eq2
    nlinarith
  have h4 : (x - 3) * (x + 2) = 0 := by
    nlinarith [h3]
  cases' (mul_eq_zero.mp h4) with h5 h6
  · -- Case where x = 3.
    have hx : x = 3 := by linarith
    have hy : y = -2 := by
      linarith [h₀, hx]
    left
    simp [hx, hy]
  · -- Case where x = -2.
    have hx : x = -2 := by linarith
    have hy : y = 3 := by 
      linarith [h₀, hx]
    right
    simp [hx, hy]