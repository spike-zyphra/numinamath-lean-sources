import Mathlib

theorem number_theory_190842 (a b c d e : ℤ) (h : ∀ x : ℤ, 7 ∣ a*x^4+b*x^3+c*x^2+d*x+e) :
    7 ∣ a ∧ 7 ∣ b ∧ 7 ∣ c ∧ 7 ∣ d ∧ 7 ∣ e := by
  have h1 := h 0
  have h2 := h 1
  have h3 := h ( -1)
  have h4 := h 2
  have h5 := h ( -2)
  have h6 := h 3
  have h7 := h ( -3)
  norm_num at h1 h2 h3 h4 h5 h6 h7
  constructor
  · -- Prove that 7 divides a
    omega
  constructor
  · -- Prove that 7 divides b
    omega
  constructor
  · -- Prove that 7 divides c
    omega
  constructor
  · -- Prove that 7 divides d
    omega
  · -- Prove that 7 divides e
    omega