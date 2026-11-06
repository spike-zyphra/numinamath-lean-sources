import Mathlib

theorem algebra_307043 (m : ℝ) (h : ∃ x, x^2 + m * x + 1 = 0 ∧ x^2 - x - m = 0) :
    m = 2 := by
  rcases h with ⟨x, h₁, h₂⟩
  have h3 : x^2 + m * x + 1 - (x^2 - x - m) = 0 := by linarith
  have h4 : (x + 1) * (1 + m) = 0 := by
    ring_nf at h3 ⊢
    linarith
  cases' (mul_eq_zero.mp h4) with h5 h6
  · -- Case where x + 1 = 0, so x = -1
    have hx : x = -1 := by linarith
    rw [hx] at h₁
    linarith
  · -- Case where 1 + m = 0, so m = -1
    have hm : m = -1 := by linarith
    rw [hm] at h₁ h₂
    have h7 : x^2 - x + 1 = 0 := by
      nlinarith
    have h9 : x^2 - x + 1 > 0 := by
      nlinarith [sq_nonneg (x - 1 / 2)]
    linarith [h7, h9]