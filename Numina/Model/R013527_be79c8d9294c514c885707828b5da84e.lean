import Mathlib

theorem algebra_2584 {a b : ℝ} (hab : a < -b) (hab' : 0 < a / b) :
    abs a - abs b + abs (a + b) + abs (a * b) = -2 * a + a * b := by
  have h1 : a + b < 0 := by linarith
  have hb : b < 0 := by
    by_contra h
    push_neg at h
    have h4 : a + b < 0 := by linarith
    have h5 : a < 0 := by nlinarith
    have h5' : a / b ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg
      · nlinarith
      · linarith
    linarith
  have ha : a < 0 := by
    by_contra h
    push_neg at h
    have hb : b < 0 := by
      by_contra h
      push_neg at h
      have h4 : a + b < 0 := by linarith
      have h5 : a < 0 := by nlinarith
      linarith
    have h5 : a / b ≤ 0 := by
      apply div_nonpos_of_nonneg_of_nonpos
      · linarith
      · linarith
    linarith
  have h2 : a * b > 0 := by
    have ha : a < 0 := by assumption
    have hb : b < 0 := by assumption
    nlinarith
  have h4 : abs a = -a := by
    rw [abs_of_neg ha]
  have h5 : abs b = -b := by
    rw [abs_of_neg hb]
  have h6 : abs (a + b) = -(a + b) := by
    rw [abs_of_neg h1]
  have h7 : abs (a * b) = a * b := by
    rw [abs_of_pos h2]
  rw [h4, h5, h6, h7]
  linarith