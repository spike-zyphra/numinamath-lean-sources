import Mathlib

theorem algebra_20187 (x : ℕ) :
    6 * 6 ^ x = 6 ^ 6 ↔ x = 5 := by
  constructor
  · -- Forward: Assume 6 * 6 ^ x = 6 ^ 6, prove x = 5
    intro h
    have h1 : 6 ^ (x + 1) = 6 ^ 6 := by
      ring_nf at h ⊢
      linarith
    have h2 : x + 1 = 6 := by
      exact Nat.pow_right_injective (by norm_num) h1
    linarith
  · -- Backward: Assume x = 5, prove 6 * 6 ^ x = 6 ^ 6
    intro h
    rw [h]
    all_goals norm_num