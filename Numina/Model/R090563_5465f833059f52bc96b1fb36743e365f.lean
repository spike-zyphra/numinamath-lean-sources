import Mathlib

theorem algebra_187407 {a : ℝ} (ha : ∃ x, x^2 + a * x + 8 = 0 ∧ x^2 + x + a = 0) :
    a = -6 := by
  rcases ha with ⟨x, h₁, h₂⟩
  have h3 : (a - 1) * x = a - 8 := by
    nlinarith

  by_cases h : a - 1 = 0
  · -- Case where a - 1 = 0, i.e., a = 1
    have ha1 : a = 1 := by linarith
    rw [ha1] at h₁
    have : x ^ 2 + (1 : ℝ) * x + 8 = 0 := by linarith
    have h4 : x ^ 2 + x + 8 = 0 := by linarith
    have h5 : (x ^ 2 + x + 8 = 0) → False := by
      intro h
      nlinarith [sq_nonneg (x + 0.25 / 1)]
    contradiction

  · -- Case where a - 1 ≠ 0
    have h4 : a - 1 ≠ 0 := by
      exact h
    have hx : x = (a - 8) / (a - 1) := by
      field_simp [(show a - 1 ≠ 0 by exact h4)]
      linarith
    rw [hx] at h₂
    have h5 : (a - 8) ^ 2 + (a - 8) * (a - 1) + a * (a - 1) ^ 2 = 0 := by
      field_simp [(show a - 1 ≠ 0 by exact h4)] at h₂
      nlinarith
    ring_nf at h5
    have h6 : (a + 6) * (a^2 - 6 * a + 12) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h6) with h7 h8
    · -- Case where a + 6 = 0
      linarith
    · -- Case where a^2 - 6a + 12 = 0
      have h9 : a^2 - 6 * a + 12 = 0 := by
        nlinarith
      nlinarith [sq_nonneg (a - 3)]