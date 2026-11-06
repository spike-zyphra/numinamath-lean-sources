import Mathlib

theorem number_theory_285387 (a b c d : ℤ) (h : ∀ x : ℤ, 5 ∣ a * x ^ 3 + b * x ^ 2 + c * x + d) :
    5 ∣ a ∧ 5 ∣ b ∧ 5 ∣ c ∧ 5 ∣ d := by
  have h1 := h 0
  have h2 := h 1
  have h3 := h (2 : ℤ)
  have h4 := h (3 : ℤ)
  have h5 := h (4 : ℤ)
  have h6 := h (5 : ℤ)
  have h7 := h (6 : ℤ)
  have h8 := h (7 : ℤ)
  have h9 := h (8 : ℤ)
  have h10 := h (9 : ℤ)
  norm_num at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  constructor
  · -- Show that 5 divides a
    omega
  constructor
  · -- Show that 5 divides b
    omega
  constructor
  · -- Show that 5 divides c
    omega
  · -- Show that 5 divides d
    omega