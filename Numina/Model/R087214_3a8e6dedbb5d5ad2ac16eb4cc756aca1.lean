import Mathlib

theorem algebra_93441 (a r : ℤ) (h₀ : a = 8) (h₁ : r ≠ 0)
    (h₂ : 5832 = a * r ^ 6) :
    a * r ^ 4 = 648 := by
  rw [h₀] at h₂ ⊢
  have h3 : r^6 = 729 := by
    nlinarith
  have h5 : r^2 = 9 := by
    have h6 : r^6 - 729 = 0 := by omega
    have h7 : (r^2 - 9) * (r^4 + 9 * r^2 + 81) = 0 := by
      ring_nf at h6 ⊢
      nlinarith
    cases' (mul_eq_zero.mp h7) with h8 h9
    · -- Case r^2 - 9 = 0, so r^2 = 9
      have h10 : r^2 = 9 := by linarith
      exact h10
    · -- Case r^4 + 9r^2 + 81 = 0
      nlinarith [sq_nonneg (r^2), sq_nonneg (r + 3), sq_nonneg (r - 3)]
  have r4 : r^4 = 81 := by
    have h : r^2 = 9 := h5
    have r4 : r^4 = (r^2) ^ 2 := by ring
    rw [r4, h]
    norm_num
  nlinarith [r4]