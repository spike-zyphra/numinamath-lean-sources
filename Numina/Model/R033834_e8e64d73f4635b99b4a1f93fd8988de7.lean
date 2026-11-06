import Mathlib

theorem algebra_4872 :
  IsLeast {z : ℕ | ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x ^ 3 + 2 * y ^ 3 = x * y ^ 2 * z} 3 := by
  constructor
  · -- Show 3 is in the set.
    use 1, 1
    all_goals
      norm_num
  · -- Show 3 is the minimum element in the set.
    intro z h
    rcases h with ⟨x, y, hx, hy, hz, heq⟩
    by_contra h'
    push_neg at h'
    have h1 : z < 3 := by linarith
    have h2 : z = 1 ∨ z = 2 := by
      interval_cases z <;> omega
    rcases h2 with (r | r)
    · -- z = 1
      have h3 : z = 1 := r
      rw [show z = 1 by omega] at heq
      have h4 : x ^ 3 + 2 * y ^ 3 ≥ 3 * x * y ^ 2 := by
        nlinarith [sq_nonneg (x - y : ℤ), sq_nonneg (y : ℤ), sq_nonneg (y - x : ℤ), sq_nonneg ((y : ℤ) ), sq_nonneg ((x ^ 2 - y ^ 2 : ℤ) ), sq_nonneg ((y ^ 2 - x ^ 2 : ℤ) ), sq_nonneg ((x - 2 * y : ℤ) ), sq_nonneg ((2 * y - x : ℤ) ), mul_pos (show 0 < (x : ℤ) by omega) (show 0 < (y : ℤ) by omega)]
      nlinarith [mul_pos (show (0 : ℕ) < x by linarith) (show (0 : ℕ) < y by linarith), mul_pos (show (0 : ℕ) < y by linarith) (show (0 : ℕ) < y by linarith)]
    · -- z = 2
      have h3 : z = 2 := r
      rw [show z = 2 by omega] at heq
      have h4 : x ^ 3 + 2 * y ^ 3 ≥ 3 * x * y ^ 2 := by
        nlinarith [sq_nonneg (x - y : ℤ), sq_nonneg (y : ℤ), sq_nonneg (y - x : ℤ), sq_nonneg ((y : ℤ) ), sq_nonneg ((x ^ 2 - y ^ 2 : ℤ) ), sq_nonneg ((y ^ 2 - x ^ 2 : ℤ) ), sq_nonneg ((x - 2 * y : ℤ) ), sq_nonneg ((2 * y - x : ℤ) ), mul_pos (show 0 < (x : ℤ) by omega) (show 0 < (y : ℤ) by omega)]
      nlinarith [mul_pos (show (0 : ℕ) < x by linarith) (show (0 : ℕ) < y by linarith), mul_pos (show (0 : ℕ) < y by linarith) (show (0 : ℕ) < y by linarith)]