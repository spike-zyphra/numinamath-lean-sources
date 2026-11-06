import Mathlib

open List

theorem algebra_2509 {a : ℝ} (ha : a < 0) : a^3 ≠ (-a)^3 := by
  have h1 : (-a)^3 = - (a^3) := by
    ring
  intro h
  rw [h1] at h
  have h2 : a^3 = 0 := by
    linarith [h]
  have h3 : a^3 = 0 := h2
  have h4 : a = 0 := by
    have h5 : a^3 = 0 := h3
    simp at h5 ⊢
    all_goals nlinarith [sq_nonneg a, h5]
  linarith [h4, ha]