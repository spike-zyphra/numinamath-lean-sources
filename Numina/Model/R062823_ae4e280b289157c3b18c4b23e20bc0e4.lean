import Mathlib

theorem number_theory_325858 :
    (∀ x y : ℤ, 5 ∣ x + 9 * y → 5 ∣ 8 * x + 7 * y) ∧
    (∀ x y z : ℤ, 11 ∣ 7 * x + 2 * y - 5 * z → 11 ∣ 3 * x - 7 * y + 12 * z) := by
  constructor
  · -- Proof for the first statement
    intros x y h
    omega
  · -- Proof for the second statement
    intros x y z h
    omega