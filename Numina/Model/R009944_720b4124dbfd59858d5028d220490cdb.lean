import Mathlib

theorem algebra_211088 (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ m n : ℕ, (-2 * a ^ n * b ^ n) ^ m + (3 * a ^ m * b ^ m) ^ n = a ^ 6 * b ^ 6 := by 
  use 3, 2
  ring_nf