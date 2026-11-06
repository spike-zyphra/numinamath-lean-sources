import Mathlib

theorem algebra_192822 (x : ℝ) :
    (∀ y : ℝ, ∃ z : ℝ, x^2 + y^2 + z^2 + 2 * x * y * z = 1) ↔ x^2 = 1 := by
  constructor
  · -- Assume that for all y, there exists a z such that the equation holds, prove x^2 = 1
    intro h
    have h1 := h 2
    rcases h1 with ⟨z1, h1⟩
    have h2 := h 0
    rcases h2 with ⟨z2, h2⟩
    have h11 : 3 * (x ^ 2 - 1) ≥ 0 := by
      nlinarith [sq_nonneg (z1 + 2 * x)]
    have hx1 : x^2 ≥ 1 := by
      linarith
    have hx2 : x^2 ≤ 1 := by
      nlinarith [sq_nonneg (z2)]
    linarith
  · -- Assume x^2 = 1, prove ∀ y : ℝ, ∃ z : ℝ, x^2 + y^2 + z^2 + 2 * x * y * z = 1
    intro hx
    have h1 : x = 1 ∨ x = -1 := by
      have h2 : x^2 = 1 := hx
      have : x = 1 ∨ x = -1 := by
        rw [sq_eq_one_iff] at h2
        tauto
      assumption
    intro y
    rcases h1 with (h | h)
    · -- x = 1
      use -y
      rw [show x = 1 by linarith]
      nlinarith
    · -- x = -1
      use y
      rw [show x = -1 by linarith]
      nlinarith