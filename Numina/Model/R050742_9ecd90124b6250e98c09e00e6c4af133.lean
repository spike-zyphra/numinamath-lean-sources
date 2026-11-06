import Mathlib

theorem number_theory_7362 (n : ℕ) (hn : n > 0) :
    ∃ x y z s : ℕ,
      x > 0 ∧ y > 0 ∧ z > 0 ∧ s > 0 ∧
      x + y + z = s ∧ x * y = z * s ∧
      ∃ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a^2 + b^2 = c^2 ∧
        a * b / 2 = 4 * x * y := by
  use 2 * n, 3 * n, n, 6 * n
  constructor
  · -- Show x > 0
    nlinarith
  constructor
  · -- Show y > 0
    nlinarith
  constructor
  · -- Show z > 0
    linarith
  constructor
  · -- Show s > 0
    nlinarith
  constructor
  · -- Show x + y + z = s
    ring
  constructor
  · -- Show x * y = z * s
    ring
  · -- Show existence of right triangle
    use 6 * n, 8 * n, 10 * n
    constructor
    · -- Show a > 0
      nlinarith
    constructor
    · -- Show b > 0
      nlinarith
    constructor
    · -- Show c > 0
      nlinarith
    constructor
    · -- Show a^2 + b^2 = c^2
      ring_nf
    · -- Show a * b / 2 = 4 * x * y
      ring_nf
      <;> omega