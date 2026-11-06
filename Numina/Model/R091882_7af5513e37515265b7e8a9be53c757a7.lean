import Mathlib

theorem algebra_196577 {a b c : ℝ} (h : (a + b + c)^2 = 3 * (a^2 + b^2 + c^2)) (h' : a + b + c = 12) :
    a = 4 := by
  have h3 : a^2 + b^2 + c^2 = 48 := by
    rw [h'] at h
    nlinarith
  have h7 : (a - b)^2 + (b - c)^2 + (c - a)^2 = 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have hab : a = b := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have hbc : b = c := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  have ha : a = 4 := by
    have h1 : a + b + c = 12 := h'
    rw [show b = a by linarith [hab], show c = a by linarith [hab, hbc]] at h1
    linarith
  exact ha