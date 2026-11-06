import Mathlib

theorem algebra_608168 :
    IsGreatest {n : ℤ | n > 0 ∧ ∃ x y z : ℤ, x > 0 ∧ y > 0 ∧ z > 0 ∧ n ^ 2 = x ^ 2 + y ^ 2 + z ^ 2 + 2 * x * y + 2 * y * z + 2 * z * x + 3 * x + 3 * y + 3 * z - 6} 8 := by
  constructor
  · -- Show 8 is in the set
    constructor
    · norm_num
    · -- Show existence of positive integers x, y, z
      use 1, 2, 4
      all_goals norm_num
  · -- Show 8 is greatest in the set
    intro n hn
    rcases hn with ⟨hn_pos, x, y, z, hx, hy, hz, heq⟩
    by_contra h
    push_neg at h
    have h1 : n ≥ 9 := by linarith
    have eq1 : n ^ 2 = (x + y + z) ^ 2 + 3 * (x + y + z) - 6 := by
      nlinarith [heq]
    have h2 : n ≤ x + y + z + 1 := by
      nlinarith [sq_nonneg (n - (x + y + z)), sq_nonneg ((x + y + z) + 1)]
    have h3 : x + y + z ≥ 8 := by
      nlinarith [h2, h1]
    have h7 : n ^ 2 ≤ (x + y + z) ^ 2 + 3 * (x + y + z) := by
      nlinarith [sq_nonneg (n - (x + y + z)), sq_nonneg ((x + y + z) + 1)]
    have h8 : x + y + z ≤ n + 1 := by
      nlinarith [sq_nonneg (n - (x + y + z)), sq_nonneg ((x + y + z) + 1)]
    nlinarith [sq_nonneg (n - 8), sq_nonneg ((x + y + z) - 7), sq_nonneg (x - 1), sq_nonneg (y - 2), sq_nonneg (z - 4)]