import Mathlib

theorem number_theory_296504 :
    ∃ a b c : ℕ, a.Prime ∧ b.Prime ∧ c.Prime ∧ a < b ∧ b < c ∧ c < 100 ∧
      ∃ r : ℚ, (b + 1) = r * (a + 1) ∧ (c + 1) = r * (b + 1) := by
  use 2, 5, 11
  constructor
  · -- a is prime
    norm_num
  constructor
  · -- b is prime
    norm_num
  constructor
  · -- c is prime
    norm_num
  constructor
  · -- a < b
    norm_num
  constructor
  · -- b < c
    norm_num
  constructor
  · -- c < 100
    norm_num
  · -- existence of r
    use 2
    constructor
    · -- (b + 1) = r * (a + 1)
      norm_num
    · -- (c + 1) = r * (b + 1)
      norm_num