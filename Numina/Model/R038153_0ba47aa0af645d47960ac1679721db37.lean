import Mathlib

theorem algebra_224438 {a b c : ℤ} (h : ∀ x : ℤ, 3 ∣ a*x^2 + b*x + c) :
    3 ∣ a ∧ 3 ∣ b ∧ 3 ∣ c := by
  have h1 := h 0
  have h2 := h 1
  have h3 := h (-1)
  have h4 := h 2
  have h5 := h (-2)
  constructor
  · -- Prove that 3 divides a
    omega
  constructor
  · -- Prove that 3 divides b
    omega
  · -- Prove that 3 divides c
    omega