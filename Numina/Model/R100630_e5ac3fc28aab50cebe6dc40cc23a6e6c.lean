import Mathlib

theorem number_theory_254742 :
    (∀ x y : ℤ, 5 ∣ x + 9 * y → 5 ∣ 8 * x + 7 * y) ∧
    (∀ x y z : ℤ, 11 ∣ 7 * x + 2 * y - 5 * z → 11 ∣ 3 * x - 7 * y + 12 * z) := by
  constructor
  · -- Assume h : 5 ∣ x + 9 * y, prove 5 ∣ 8 * x + 7 * y
    intro x y h
    omega
  · -- Assume h : 11 ∣ 7 * x + 2 * y - 5 * z, prove 11 ∣ 3 * x - 7 * y + 12 * z
    intro x y z h
    omega