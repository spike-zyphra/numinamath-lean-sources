import Mathlib

open Real

theorem number_theory_97200 (k : ℕ) (hk : k = 16) :
    (7 / 51 : ℝ) = 2 * ∑' n : ℕ, (1 : ℝ) / k ^ (2 * n + 1) + 3 * ∑' n : ℕ, (1 : ℝ) / k ^ (2 * n + 2) := by 
  rw [hk]
  have h1 : ∀ n : ℕ, (1 : ℝ) / (16 : ℕ) ^ (2 * n + 1) = (1 / 16) * (1 / 256) ^ n := by
    intro n
    induction n with
    | zero => 
      norm_num
    | succ n ih =>
      simp [pow_succ, pow_mul] at ih ⊢ 
      field_simp at ih ⊢
      <;> nlinarith
  have h2 : ∀ n : ℕ, (1 : ℝ) / (16 : ℕ) ^ (2 * n + 2) = (1 / 256) * (1 / 256) ^ n := by 
    intro n
    induction n with
    | zero => 
      norm_num
    | succ n ih =>
      simp [pow_succ, pow_mul] at ih ⊢ 
      field_simp at ih ⊢
      <;> nlinarith 
  rw [tsum_congr h1]
  rw [tsum_mul_left, tsum_geometric_of_lt_one]
  rw [tsum_congr h2]
  rw [tsum_mul_left, tsum_geometric_of_lt_one]
  all_goals norm_num