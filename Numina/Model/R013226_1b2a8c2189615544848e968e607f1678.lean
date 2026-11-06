import Mathlib

theorem algebra_244299 {a b c d : ℝ} (h₀ : a + c = 4) (h₁ : a * c + b + d = 6)
    (h₂ : a * d + b * c = 5) (h₃ : b * d = 2) :
    (a, b, c, d) = (3, 2, 1, 1) ∨ (a, b, c, d) = (1, 1, 3, 2) := by
  have hc : c = 4 - a := by linarith
  rw [hc] at h₁
  have eq1 : b + d = 6 - 4 * a + a ^ 2 := by nlinarith
  rw [hc] at h₂
  have h4 : (a - 3) * (a - 1) = 0 := by
    nlinarith [sq_nonneg (a - 1), sq_nonneg (a - 3), sq_nonneg (b - 2), sq_nonneg (b - 1), sq_nonneg (d - 1), sq_nonneg (d - 2), sq_nonneg (a - 3), sq_nonneg (c - 1), sq_nonneg (c - 3)]
  cases (mul_eq_zero.mp h4) with
  | inl ha3 =>
    have ha3' : a = 3 := by linarith
    have hc1 : c = 1 := by
      rw [show a = 3 by linarith] at hc
      linarith [hc]
    have hbd : b = 2 := by
      nlinarith [h₂, ha3', hc1]
    have hda : d = 1 := by
      nlinarith [eq1, hbd]
    left
    simp [ha3', hbd, hc1, hda]
  | inr ha1 =>
    have ha1' : a = 1 := by linarith
    have hc3 : c = 3 := by
      rw [show a = 1 by linarith] at hc
      linarith [hc]
    have hbd : b = 1 := by
      nlinarith [h₂, ha1', hc3]
    have hda : d = 2 := by
      nlinarith [eq1, hbd]
    right
    simp [ha1', hbd, hc3, hda]