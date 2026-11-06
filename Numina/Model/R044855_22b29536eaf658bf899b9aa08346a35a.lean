import Mathlib

theorem algebra_285435 (a b c d e : ℤ) (h : ∀ x : ℤ, 7 ∣ a * x ^ 4 + b * x ^ 3 + c * x ^ 2 + d * x + e) :
    7 ∣ a ∧ 7 ∣ b ∧ 7 ∣ c ∧ 7 ∣ d ∧ 7 ∣ e := by

  have eq0 := h 0
  have eq1 := h 1
  have eq2 := h (-1)
  have eq3 := h 2
  have eq4 := h (-2)
  have eq5 := h 3
  have eq6 := h 4

  constructor
  · -- Show that 7 divides a
    omega

  constructor
  · -- Show that 7 divides b
    omega

  constructor
  · -- Show that 7 divides c
    omega

  constructor
  · -- Show that 7 divides d
    omega

  · -- Show that 7 divides e
    omega