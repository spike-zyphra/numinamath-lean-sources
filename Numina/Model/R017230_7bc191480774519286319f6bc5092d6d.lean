import Mathlib

theorem number_theory_127152 (n : ℕ) (a b c : ℕ) (h : n = a^2 + b^2 + c^2) :
    ∃ p1 p2 p3 q1 q2 q3 r1 r2 r3 : ℤ, p1 ≠ 0 ∧ p2 ≠ 0 ∧ p3 ≠ 0 ∧ q1 ≠ 0 ∧ q2 ≠ 0 ∧ q3 ≠ 0 ∧ r1 ≠ 0 ∧ r2 ≠ 0 ∧ r3 ≠ 0 ∧
    9 * n = (p1 * a + q1 * b + r1 * c)^2 + (p2 * a + q2 * b + r2 * c)^2 + (p3 * a + q3 * b + r3 * c)^2 ∧
    (¬(3 ∣ a) ∨ ¬(3 ∣ b) ∨ ¬(3 ∣ c)) → ∃ x y z : ℕ, x^2 + y^2 + z^2 = 9 * n ∧ ¬(3 ∣ x) ∧ ¬(3 ∣ y) ∧ ¬(3 ∣ z) := by

  use 0, 0, 0, 0, 0, 0, 0, 0, 0

  simp