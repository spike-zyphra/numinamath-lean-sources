import Mathlib

open Real Set

theorem algebra_310459 (a b : ℝ) (ha : a^2 + 2 * b^2 ≠ 0) (hb : 2 * a^2 + b^2 ≠ 0)
    (t : ℝ) (ht : t = a^2 / (a^2 + 2 * b^2) + b^2 / (2 * a^2 + b^2)) :
    t ≥ 2 / 3 := by
  rw [ht]
  have h1 : a^2 / (a^2 + 2 * b^2) + b^2 / (2 * a^2 + b^2) - 2 / 3 ≥ 0 := by 
    have h2 : 0 < (a^2 + 2 * b^2) * (2 * a^2 + b^2) := by
      apply mul_pos
      · -- Show that $a^2 + 2b^2 > 0$
        by_contra h
        push_neg at h
        have h3 : a^2 + 2 * b^2 ≤ 0 := by linarith
        have h4 : a^2 ≥ 0 := sq_nonneg a
        have h5 : b^2 ≥ 0 := sq_nonneg b
        have h6 : a^2 + 2 * b^2 ≥ 0 := by nlinarith
        have h7 : a^2 + 2 * b^2 = 0 := by linarith
        contradiction
      · -- Show that $2a^2 + b^2 > 0$
        by_contra h
        push_neg at h
        have h3 : 2 * a^2 + b^2 ≤ 0 := by linarith
        have h4 : a^2 ≥ 0 := sq_nonneg a
        have h5 : b^2 ≥ 0 := sq_nonneg b
        have h6 : 2 * a^2 + b^2 ≥ 0 := by nlinarith
        have h7 : 2 * a^2 + b^2 = 0 := by linarith
        contradiction
    have h3 : a^2 / (a^2 + 2 * b^2) + b^2 / (2 * a^2 + b^2) - 2 / 3 =
        (2 * (a^2 - b^2) ^ 2) / (3 * (a^2 + 2 * b^2) * (2 * a^2 + b^2)) := by
      field_simp
      ring
    have h4 : (2 * (a^2 - b^2) ^ 2) / (3 * (a^2 + 2 * b^2) * (2 * a^2 + b^2)) ≥ 0 := by
      apply div_nonneg
      · -- Show that 2 * (a^2 - b^2)^2 ≥ 0
        nlinarith [sq_nonneg (a^2 - b^2)]
      · -- Show that 3 * (a^2 + 2 * b^2) * (2 * a^2 + b^2) ≥ 0
        nlinarith [h2, sq_nonneg (a), sq_nonneg (b)]
    linarith [h3, h4]
  linarith