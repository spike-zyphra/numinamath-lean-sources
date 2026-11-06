import Mathlib

theorem algebra_187011 {x y : ℝ} (h₀ : x^3 + y^3 = 7) (h₁ : x^3 * y^3 = -8) :
    (x = 2 ∧ y = -1) ∨ (x = -1 ∧ y = 2) := by
  have h2 : x * y = -2 := by
    have h3 : x^3 * y^3 = (x * y) ^ 3 := by
      ring
    rw [h3] at h₁
    have h4 : (x * y) ^ 3 + 8 = 0 := by
      linarith
    have h5 : x * y + 2 = 0 := by
      have h6 : (x * y + 2) * ((x * y) ^ 2 - (x * y) * 2 + 4) = 0 := by
        ring_nf at h4 ⊢
        linarith
      cases' (mul_eq_zero.mp h6) with h7 h8
      · linarith
      · -- Let's show that the quadratic is non-zero
        nlinarith [sq_nonneg ((x * y) - 1)]
    linarith
  have h3 : x + y = 1 := by
    have h4 : x^3 + y^3 = (x + y)^3 - 3 * (x + y) * (x * y) := by
      ring
    rw [h4] at h₀
    rw [h2] at h₀
    have h5 : (x + y)^3 + 6 * (x + y) = 7 := by
      linarith
    have h6 : (x + y) = 1 := by
      have h7 : (x + y) ^ 3 + 6 * (x + y) - 7 = 0 := by
        linarith
      have h8 : ((x + y) - 1) * ((x + y)^2 + (x + y) + 7) = 0 := by 
        nlinarith
      cases' (mul_eq_zero.mp h8) with h9 h10
      · linarith
      · -- The quadratic equation has no real solutions
        nlinarith [sq_nonneg ((x + y) + 1 / 2)]
    exact h6
  have h4 : x^2 - x - 2 = 0 := by
    have h8 : y = 1 - x := by
      linarith
    rw [h8] at h2
    nlinarith
  have h5 : (x - 2) * (x + 1) = 0 := by 
    nlinarith
  cases' (mul_eq_zero.mp h5) with h6 h7
  · -- If x = 2, then y = -1 from (x + y = 1)
    have hx : x = 2 := by
      linarith
    have hy : y = -1 := by 
      nlinarith
    left
    exact ⟨hx, hy⟩
  · -- If x = -1, then y = 2 from (x + y = 1)
    have hx : x = -1 := by
      linarith
    have hy : y = 2 := by 
      nlinarith
    right
    exact ⟨hx, hy⟩