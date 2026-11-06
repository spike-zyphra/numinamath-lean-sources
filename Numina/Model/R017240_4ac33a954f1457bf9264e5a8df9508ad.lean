import Mathlib

theorem algebra_309833 {k : ℝ} (h : ∃ x, x^2 + k * x - 12 = 0 ∧ 3 * x^2 - 8 * x - 3 * k = 0) :
    k = 1 := by
  rcases h with ⟨x, h1, h2⟩
  have h3 : k = (3 * x^2 - 8 * x) / 3 := by
    linarith
  rw [h3] at h1
  have h4 : 3 * x^3 - 5 * x^2 - 36 = 0 := by
    ring_nf at h1 ⊢
    nlinarith
  have h5 : (x - 3) * (3 * x^2 + 4 * x + 12) = 0 := by
    nlinarith [h4]
  cases' (mul_eq_zero.1 h5) with h6 h7
  · -- x - 3 = 0, so x = 3
    have hx : x = 3 := by linarith
    rw [hx] at h3
    nlinarith
  · -- 3 * x^2 + 4 * x + 12 = 0
    have h8 : 3 * x^2 + 4 * x + 12 = 0 := by
      linarith
    have h9 : (3 * x^2 + 4 * x + 12 : ℝ) > 0 := by
      nlinarith [sq_nonneg (x + 2 / 3)]
    nlinarith