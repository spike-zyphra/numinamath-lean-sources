import Mathlib

theorem algebra_223023 {x y z a : ℝ} (h1 : x + y + z = a) (h2 : x^2 + y^2 + z^2 = a^2)
    (h3 : x^3 + y^3 + z^3 = a^3) :
    (x = 0 ∧ y = 0 ∧ z = 0) ∨ (x = 0 ∧ y = 0) ∨ (x = 0 ∧ z = 0) ∨ (y = 0 ∧ z = 0) := by

  have h4 : x * y + x * z + y * z = 0 := by
    have h41 : x^2 + y^2 + z^2 = (x + y + z)^2 - 2 * (x * y + x * z + y * z) := by
      ring
    rw [h1] at h41
    have h42 : x^2 + y^2 + z^2 = a^2 := h2
    linarith

  have h5 : x * y * z = 0 := by
    have h61 : x^3 + y^3 + z^3 - 3 * (x * y * z) = (x + y + z) * ((x^2 + y^2 + z^2) - (x * y + x * z + y * z)) := by
      ring
    rw [h1, h2, h4] at h61
    have h62 : x^3 + y^3 + z^3 = a^3 := h3
    linarith

  cases' (mul_eq_zero.mp h5) with h6 h7
  · cases' (mul_eq_zero.mp h6) with h8 h9
    · -- x = 0
      have hx0 : x = 0 := h8
      have h10 : y * z = 0 := by
        rw [hx0] at h4
        nlinarith
      cases' (mul_eq_zero.mp h10) with h11 h12
      · -- y = 0
        have hy0 : y = 0 := h11
        simp [hx0, hy0]
      · -- z = 0
        have hz0 : z = 0 := h12
        have hx0 : x = 0 := hx0
        simp [hx0, hz0]
    · -- y = 0
      have hy0 : y = 0 := h9
      have h10 : x * z = 0 := by
        rw [hy0] at h4
        nlinarith
      cases' (mul_eq_zero.mp h10) with h11 h12
      · -- x = 0
        have hx0 : x = 0 := h11
        simp [hx0, hy0]
      · -- z = 0
        have hz0 : z = 0 := h12
        simp [hy0, hz0]
  · -- z = 0
    have hz0 : z = 0 := h7
    have h10 : x * y = 0 := by
      rw [show z = 0 by linarith [hz0]] at h4
      nlinarith
    cases' (mul_eq_zero.mp h10) with h11 h12
    · -- x = 0
      have hx0 : x = 0 := h11
      simp [hx0, hz0]
    · -- y = 0
      have hy0 : y = 0 := h12
      simp [hy0, hz0]