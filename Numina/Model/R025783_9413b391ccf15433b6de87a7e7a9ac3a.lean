import Mathlib

theorem algebra_93997 (a r : ℝ) (h₀ : a * (1 + r) = 7) (h₁ : a * (1 + r + r^2 + r^3 + r^4 + r^5) = 91) :
    a * (1 + r + r^2 + r^3) = 28 := by
  have eq1 : a * (1 + r + r^2 + r^3 + r^4 + r^5) = a * (1 + r) * (r^4 + r^2 + 1) := by
    ring_nf
  rw [eq1] at h₁
  have h3 : a * (1 + r) * (r^4 + r^2 + 1) = 7 * (r^4 + r^2 + 1) := by
    have h4 : a * (1 + r) = 7 := h₀
    calc
      a * (1 + r) * (r^4 + r^2 + 1) = (a * (1 + r)) * (r^4 + r^2 + 1) := by ring
      _ = 7 * (r^4 + r^2 + 1) := by rw [h4]
  rw [h3] at h₁
  have h4 : r^4 + r^2 + 1 = 13 := by
    nlinarith
  have h5 : r^2 = 3 := by
    have h6 : r^4 + r^2 - 12 = 0 := by
      nlinarith
    have h7 : (r^2 - 3) * (r^2 + 4) = 0 := by
      nlinarith [h6]
    cases' (mul_eq_zero.1 h7) with h8 h9
    · -- r^2 - 3 = 0, so r^2 = 3
      linarith
    · -- r^2 + 4 = 0 => contradiction as r is real
      have h10 : r^2 + 4 > 0 := by
        nlinarith [sq_nonneg r]
      nlinarith
  have eq2 : a * (1 + r + r^2 + r^3) = a * (1 + r) * (1 + r^2) := by
    ring_nf
  have h6 : a * (1 + r) = 7 := h₀
  calc
    a * (1 + r + r^2 + r^3) = a * (1 + r) * (1 + r^2) := by rw [eq2]
    _ = (a * (1 + r)) * (1 + r^2) := by ring
    _ = 7 * (1 + r^2) := by rw [h6]
    _ = 7 * (1 + 3) := by rw [h5]
    _ = 28 := by norm_num