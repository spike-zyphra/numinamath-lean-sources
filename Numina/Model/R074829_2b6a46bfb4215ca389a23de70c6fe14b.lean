import Mathlib

theorem number_theory_222206 (n : ℕ) (h₀ : n = 3000003) :
    ∃ a b, a < 10 ∧ b < 10 ∧ 13 ∣ n + 100 * a + 10000 * b := by 
  rw [h₀]
  use 8, 0
  all_goals norm_num