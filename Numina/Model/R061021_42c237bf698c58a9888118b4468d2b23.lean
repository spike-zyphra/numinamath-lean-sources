import Mathlib

theorem algebra_187235 {x y : ℝ} (h₀ : x^3 + y^3 = 7) (h₁ : x * y * (x + y) = -2) :
    (x = 2 ∧ y = -1) ∨ (x = -1 ∧ y = 2) := by

  have h3 : x^3 + y^3 = (x + y) ^ 3 - 3 * (x * y * (x + y)) := by
    ring

  rw [h₀, h₁] at h3

  have h2 : (x + y) ^ 3 = 1 := by
    linarith

  have h4 : x + y = 1 := by
    have h5 : (x + y) ^ 3 = 1 := h2

    have h6 : (x + y) ^ 3 - 1 = 0 := by linarith [h5]

    have h7 : (x + y - 1) * ((x + y) ^ 2 + (x + y) + 1) = 0 := by 
      ring_nf at h6 ⊢
      linarith

    cases' (mul_eq_zero.mp h7) with h8 h9

    · -- Case where x + y - 1 = 0, so x + y = 1.
      linarith

    · -- Case where (x + y)^2 + (x + y) + 1 = 0.
      have h10 : (x + y) ^ 2 + (x + y) + 1 > 0 := by
        nlinarith [sq_nonneg (x + y + 1 / 2)]

      have h11 : (x + y) ^ 2 + (x + y) + 1 = 0 := by
        nlinarith

      linarith

  have h5 : x * y = -2 := by
    rw [h4] at h₁
    nlinarith

  have h6 : x ^ 2 - x - 2 = 0 := by
    have h7 : y = 1 - x := by linarith
    rw [h7] at h5
    nlinarith

  have h7 : (x = 2 ∨ x = -1) := by
    have h8 : x ^ 2 - x - 2 = 0 := h6
    have h9 : (x - 2) * (x + 1) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h9) with h10 h11
    · -- Case where x = 2
      left
      linarith
    · -- Case where x = -1
      right
      linarith

  cases' h7 with hx1 hx2

  · -- Case where x = 2.
    have h8 : y = -1 := by
      nlinarith [h4]
    left
    exact ⟨hx1, h8⟩

  · -- Case where x = -1
    have h8 : y = 2 := by
      nlinarith [h4]
    right
    exact ⟨hx2, h8⟩