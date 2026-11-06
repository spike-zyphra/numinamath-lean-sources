import Mathlib

theorem algebra_105478 {x y : ℝ} (h1 : x^2 - y^2 = 16) (h2 : 3 * x * y^2 + x^3 = 260) :
    (x = 5 ∧ y = 3) ∨ (x = 5 ∧ y = -3) := by

  have h3 : y^2 = x^2 - 16 := by linarith

  rw [h3] at h2

  have h4 : x^3 - 12 * x - 65 = 0 := by
    nlinarith [h2]

  have h5 : (x - 5) * (x^2 + 5 * x + 13) = 0 := by
    nlinarith [h4]

  cases' (mul_eq_zero.mp h5) with h6 h7

  · -- Case x - 5 = 0, so x = 5
    have hx : x = 5 := by linarith

    have hy : y^2 = 9 := by
      rw [hx] at h3
      nlinarith

    have h8 : y = 3 ∨ y = -3 := by
      have h9 : y^2 - 9 = 0 := by linarith

      have h10 : (y - 3) * (y + 3) = 0 := by
        nlinarith

      cases' (mul_eq_zero.mp h10) with h11 h12

      · -- y - 3 = 0
        left
        linarith

      · -- y + 3 = 0
        right
        linarith

    cases' h8 with h9 h10

    · -- y = 3
      left
      exact ⟨hx, h9⟩

    · -- y = -3
      right
      exact ⟨hx, h10⟩

  · -- Case x^2 + 5x + 13 = 0
    have h8 : x^2 + 5 * x + 13 > 0 := by
      nlinarith [sq_nonneg (x + 5 / 2)]

    nlinarith