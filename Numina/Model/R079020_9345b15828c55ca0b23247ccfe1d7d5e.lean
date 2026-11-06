import Mathlib

theorem algebra_250123 (a d : ℚ) (h₀ : d ≠ 0) (h₁ : (a + 2 * d) ^ 2 = a * (a + 8 * d)) :
    (a + a + 2 * d + a + 8 * d) / (a + d + a + 3 * d + a + 9 * d) = 13 / 16 := by
  have h2 : 4 * d^2 - 4 * a * d = 0 := by
    linarith [h₁]
  have h3 : 4 * d * (d - a) = 0 := by
    linarith
  cases' (mul_eq_zero.mp h3) with h4 h5
  · -- Case h4: 4 * d = 0, so d = 0, which contradicts h₀: d ≠ 0
    have h6 : d = 0 := by
      linarith
    contradiction
  · -- Case h5: d - a = 0, so a = d
    have ha : a = d := by
      linarith
    have num_eq : a + a + 2 * d + a + 8 * d = 13 * d := by
      rw [ha]
      linarith
    have denom_eq : a + d + a + 3 * d + a + 9 * d = 16 * d := by
      rw [ha]
      linarith
    rw [num_eq, denom_eq]
    have h7 : d ≠ 0 := h₀
    field_simp [h7]
    <;> linarith