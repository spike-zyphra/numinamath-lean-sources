import Mathlib

open Real

theorem algebra_216008 : (∑' n : ℕ, (-1 : ℝ)^n * (2^(n + 1))/(3^(n + 1))) * (∑' n : ℕ, (-1 : ℝ)^n * (3^(n + 1))/(5^(n + 1))) = 0.15 := by
  have h1 : ∑' n : ℕ, (-1 : ℝ) ^ n * (2 ^ (n + 1) ) / (3 ^ (n + 1) ) = 2 / 5 := by
    have h2 : ∀ n : ℕ, (-1 : ℝ) ^ n * (2 ^ (n + 1) ) / (3 ^ (n + 1) ) = 2 / 3 * (-2 / 3) ^ n := by
      intro n
      induction n with
      | zero =>
        norm_num
      | succ n ih =>
        simp [pow_succ, pow_mul] at ih ⊢
        field_simp at ih ⊢
        ring_nf at ih ⊢
        <;> linarith
    rw [tsum_congr h2]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
    all_goals norm_num
  have h3 : ∑' n : ℕ, (-1 : ℝ) ^ n * (3 ^ (n + 1) ) / (5 ^ (n + 1) ) = 3 / 8 := by
    have h4 : ∀ n : ℕ, (-1 : ℝ) ^ n * (3 ^ (n + 1) ) / (5 ^ (n + 1) ) = 3 / 5 * (-3 / 5) ^ n := by
      intro n
      induction n with
      | zero =>
        norm_num
      | succ n ih =>
        simp [pow_succ, pow_mul] at ih ⊢
        field_simp at ih ⊢
        ring_nf at ih ⊢
        <;> linarith
    rw [tsum_congr h4]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
    all_goals norm_num
  rw [h1, h3]
  norm_num