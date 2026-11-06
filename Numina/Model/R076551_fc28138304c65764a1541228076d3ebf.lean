import Mathlib

theorem algebra_600820 :
    ∃ a b c : ℤ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      ∃ p q : Polynomial ℤ, (X * (X - a) * (X - b) * (X - c) + 1) =
        p * q := by
  use 1, 2, 3
  constructor
  · norm_num -- a ≠ 0
  constructor
  · norm_num -- b ≠ 0
  constructor
  · norm_num -- c ≠ 0
  constructor
  · norm_num -- a ≠ b
  constructor
  · norm_num -- a ≠ c
  constructor
  · norm_num -- b ≠ c
  · use X ^ 2 + (-3) * X + 1, X ^ 2 + (-3) * X + 1
    ring_nf
    <;> norm_num
    <;> ring