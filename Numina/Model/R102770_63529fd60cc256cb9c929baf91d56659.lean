import Mathlib

theorem algebra_25770
    (a b c : ℝ)
    (h₀ : 0 < a)
    (h₁ : 0 < b)
    (h₂ : 0 < c)
    (h₃ : a * b - c = 3)
    (h₄ : a * b * c = 18) :
    a * b / c = 2 := by
  have h5 : a * b = c + 3 := by linarith
  have h6 : (a * b) * c = 18 := by linarith
  rw [h5] at h6
  have h7 : c ^ 2 + 3 * c - 18 = 0 := by
    nlinarith
  have h8 : (c - 3) * (c + 6) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h8) with h9 h10
  · -- First case: c - 3 = 0, so c = 3
    have hc : c = 3 := by linarith
    have hab : a * b = 6 := by
      rw [hc] at h5
      linarith
    rw [hab, hc]
    all_goals norm_num
  · -- Second case: c + 6 = 0, so c = -6, which contradicts c > 0
    have hc : c = -6 := by linarith
    nlinarith