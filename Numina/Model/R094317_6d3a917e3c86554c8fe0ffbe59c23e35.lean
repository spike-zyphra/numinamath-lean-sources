import Mathlib

open Real

theorem algebra_93026 (a : ℕ → ℝ) (ha : a 0 = 4) (h : ∀ n, a (n + 1) = a n * (-2 / 3)) :
    ∑' n, a n = 2.4 := by 
  have h1 : ∀ n, a n = 4 * (-2 / 3) ^ n := by 
    intro n
    induction n with
    | zero =>
      simp [ha]
    | succ n ih =>
      have h2 : a (n + 1) = a n * (-2 / 3) := h n
      rw [h2]
      rw [ih]
      simp [pow_succ]
      all_goals ring_nf
  rw [tsum_congr h1]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
  all_goals norm_num
  all_goals norm_num [abs_lt]