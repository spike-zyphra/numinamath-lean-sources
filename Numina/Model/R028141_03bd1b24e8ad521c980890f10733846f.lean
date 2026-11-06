import Mathlib

open Real

theorem algebra_14866 {S : ℝ → ℝ} (hS : ∀ r, S r = ∑' n : ℕ, 12 * r ^ n)
    (a : ℝ) (ha : -1 < a ∧ a < 1) (hS1 : S a * S (-a) = 2016) :
    S a + S (-a) = 336 := by 
  have h1 : S a = 12 / (1 - a) := by 
    rw [hS a]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
    · ring
    all_goals
      have h2 : abs a < 1 := by
        rw [abs_lt]
        constructor
        · linarith [ha.1]
        · linarith [ha.2]
      simpa using h2
  have h3 : S (-a) = 12 / (1 + a) := by 
    rw [hS (-a)]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
    · ring
    all_goals
      have h4 : abs (-a) < 1 := by
        rw [abs_lt]
        constructor
        · linarith [ha.2]
        · linarith [ha.1]
      simpa using h4
  rw [h1, h3] at hS1
  have h4 : 1 - a^2 = (1 / 14 : ℝ) := by 
    field_simp [(show (1 - a) ≠ 0 by nlinarith [ha.2]), (show (1 + a) ≠ 0 by nlinarith [ha.1])] at hS1 ⊢
    nlinarith [sq_pos_of_pos (show (0 : ℝ) < 14 by norm_num), sq_nonneg a]
  have h5 : S a + S (-a) = 24 / (1 - a^2) := by 
    rw [h1, h3]
    have h6 : 1 - a^2 = (1 - a) * (1 + a) := by 
      ring
    rw [h6]
    field_simp [(show (1 - a) ≠ 0 by nlinarith [ha.2]), (show (1 + a) ≠ 0 by nlinarith [ha.1]), 
      (show (1 + a) ≠ 0 by nlinarith [ha.1]), (show (1 - a) ≠ 0 by nlinarith [ha.2])]
    <;> ring
  rw [h5, h4]
  norm_num
  all_goals linarith