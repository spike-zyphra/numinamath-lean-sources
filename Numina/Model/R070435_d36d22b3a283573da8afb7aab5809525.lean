import Mathlib

theorem algebra_213545 {a : ℝ} (ha : a^2 / 3 - 3 / a^2 = 6) :
    (a^12 - 729) / (27 * a^6) = 234 := by
  have h1 : a ≠ 0 := by
    by_contra h
    rw [h] at ha
    norm_num at ha
  have h2 : a^4 - 18 * a^2 - 9 = 0 := by
    field_simp [pow_two, pow_succ] at ha
    nlinarith
  have h3 : a^4 = 18 * a^2 + 9 := by
    linarith
  have h4 : a^6 = 333 * a^2 + 162 := by
    calc
      a^6 = a^2 * a^4 := by ring
      _   = a^2 * (18 * a^2 + 9) := by rw [h3]
      _   = 18 * a^4 + 9 * a^2 := by ring
      _   = 18 * (18 * a^2 + 9) + 9 * a^2 := by rw [h3]
      _   = 333 * a^2 + 162 := by ring
  have h5 : a^12 = (333 * a^2 + 162)^2 := by
    calc
      a^12 = (a^6)^2 := by ring
      _    = (333 * a^2 + 162)^2 := by rw [h4]
  have h6 : a^6 ≠ 0 := by
    intro h
    have : a = 0 := by
      have h1 : a^6 = 0 := by linarith
      have h2 : a^6 = 0 := h1
      have : a = 0 := by
        have h3 : a^6 = 0 := h2
        simp at h3 ⊢
        exact h3
      exact this
    contradiction
  field_simp [h6]
  nlinarith [h2, sq_nonneg (a^2 - 9), sq_nonneg (a^2 + 9), sq_nonneg (a^2 - 3), sq_nonneg (a^2 + 3), sq_nonneg (a^2 - 1), sq_nonneg (a^2 + 1)]