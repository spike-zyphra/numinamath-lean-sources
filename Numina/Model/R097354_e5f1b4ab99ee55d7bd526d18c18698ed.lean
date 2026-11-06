import Mathlib

theorem algebra_308874 {a b c : ℝ} (h : a + b + c = 1) (h1 : b^2 + c^2 - 4 * a * c + 6 * c + 1 = 0) :
    a * b * c = 0 := by
  have ha : a = 1 - b - c := by linarith
  rw [ha] at h1
  have h3 : (b + 2 * c) ^ 2 + (c + 1) ^ 2 = 0 := by nlinarith
  have h4 : (b + 2 * c) ^ 2 ≥ 0 := by apply sq_nonneg
  have h5 : (c + 1) ^ 2 ≥ 0 := by apply sq_nonneg
  have h6 : (b + 2 * c) ^ 2 = 0 := by linarith
  have h7 : (c + 1) ^ 2 = 0 := by linarith
  have h8 : b + 2 * c = 0 := by
    rw [sq_eq_zero_iff] at h6
    exact h6
  have h9 : c + 1 = 0 := by
    rw [sq_eq_zero_iff] at h7
    exact h7
  have hc1 : c = -1 := by linarith
  have hb2 : b = 2 := by
    rw [hc1] at h8
    linarith
  have ha0 : a = 0 := by
    rw [hb2, hc1] at h
    linarith
  simp [ha0]