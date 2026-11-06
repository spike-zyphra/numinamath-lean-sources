import Mathlib

theorem algebra_219 {a b : ℝ}(h : a * (2 * Real.pi)^3 + b * (2 * Real.pi) + 1 = 0) :
    4 * a * Real.pi^3 + b * Real.pi + 5 + 1 / 2 = 5 := by
  have h1 : a * (2 * Real.pi) ^ 3 + b * (2 * Real.pi) + 1 = 0 := h
  have h2 : 4 * a * Real.pi^3 + b * Real.pi = -1 / 2 := by
    have h_eq : a * (2 * Real.pi)^3 + b * (2 * Real.pi) + 1 = 0 := h
    have eq1 : a * (2 * Real.pi)^3 + b * (2 * Real.pi) + 1 = 8 * a * Real.pi^3 + 2 * b * Real.pi + 1 := by
      ring_nf
      <;> simp [Real.pi_pos]
      <;> ring
    rw [eq1] at h_eq
    linarith
  linarith [h2]