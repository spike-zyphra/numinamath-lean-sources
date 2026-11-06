import Mathlib

theorem algebra_292446 {a b : ℝ} (h : a + b = a * b) :
    (a^3 + b^3 - a^3 * b^3)^3 + 27 * a^6 * b^6 = 0 := by

  have h1 : a^3 + b^3 = (a * b)^3 - 3 * (a * b)^2 := by
    have h2 : a + b = a * b := h
    have h3 : a^3 + b^3 = ((a + b) ^ 3 - 3 * (a * b) * (a + b)) := by
      ring
    rw [h3]
    rw [h2]
    all_goals ring

  have h2 : a^3 + b^3 - a^3 * b^3 = -3 * (a * b)^2 := by
    linarith [h1]

  have h3 : (a^3 + b^3 - a^3 * b^3) ^ 3 = -27 * (a^6) * (b^6) := by
    rw [h2]
    ring_nf

  rw [h3]
  all_goals ring