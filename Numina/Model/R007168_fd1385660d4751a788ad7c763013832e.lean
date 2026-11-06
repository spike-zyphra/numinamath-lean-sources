import Mathlib

theorem algebra_238749 (total_games : ℕ) (h : total_games = 15 + 5) (wins : ℕ)
    (hwins : wins = 9 + 5) :
    (wins / total_games : ℝ) * 100 = 70 := by
  rw [h, hwins]
  norm_num
  <;> ring_nf <;> norm_num