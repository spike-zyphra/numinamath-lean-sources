import Mathlib

theorem algebra_16204 : 
  (∑' (i : ℕ), (5 : ℝ) / 10 ^ i.succ) + (∑' (i : ℕ), (1 : ℝ) / 10 ^ i.succ) - (∑' (i : ℕ), (3 : ℝ) / 10 ^ i.succ) = 1 / 3 := by

  have h1 : (∑' (i : ℕ), (5 : ℝ) / 10 ^ i.succ) = 5 / 9 := by
    have h : ∀ i : ℕ, (5 : ℝ) / 10 ^ i.succ = 5 / 10 * (1 / 10 : ℝ) ^ i := by
      intro i
      simp [pow_succ, mul_comm]
      <;> ring
    rw [tsum_congr h]
    rw [tsum_mul_left, tsum_geometric_of_lt_one]
    all_goals norm_num

  have h2 : (∑' (i : ℕ), (1 : ℝ) / 10 ^ i.succ) = 1 / 9 := by
    have h : ∀ i : ℕ, (1 : ℝ) / 10 ^ i.succ = 1 / 10 * (1 / 10 : ℝ) ^ i := by
      intro i 
      simp [pow_succ, mul_comm]
      <;> ring
    rw [tsum_congr h]
    rw [tsum_mul_left, tsum_geometric_of_lt_one]
    all_goals norm_num

  have h3 : (∑' (i : ℕ), (3 : ℝ) / 10 ^ i.succ) = 1 / 3 := by 
    have h : ∀ i : ℕ, (3 : ℝ) / 10 ^ i.succ = 3 / 10 * (1 / 10 : ℝ) ^ i := by 
      intro i 
      simp [pow_succ, mul_comm]
      <;> ring 
    rw [tsum_congr h]
    rw [tsum_mul_left, tsum_geometric_of_lt_one]
    all_goals norm_num

  rw [h1, h2, h3]
  all_goals norm_num