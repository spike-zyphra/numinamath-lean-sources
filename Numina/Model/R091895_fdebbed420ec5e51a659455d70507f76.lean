import Mathlib

open Real

theorem calculus_22269 {s r : ℝ}
    (hs : s = 2 / sqrt 3 - 1)
    (hr : r = (9 - 4 * sqrt 3) / 33) :
    ∃ a b c d : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧
      r = (a - b * sqrt c) / d := by
  use 9, 4, 3, 33
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · rw [hr]
    all_goals norm_num
    <;> ring_nf <;> norm_num
    <;> ring