import Mathlib

theorem algebra_21049 (total_games : ℕ) (h : total_games ≠ 0) (wins : ℕ)
    (h_wins : wins = total_games * (2 / 9 : ℚ)) (losses : ℕ)
    (h_losses : losses = total_games - wins) (h_losses1 : losses = wins + 15) :
    total_games = 27 := by
  have eq1 : (wins : ℚ) = (total_games : ℚ) * (2 / 9 : ℚ) := by 
    linarith [h_wins]
  have eq2 : (9 * (wins : ℚ) = 2 * (total_games : ℚ)) := by
    linarith [eq1]
  have eq3 : 9 * (wins : ℕ) = 2 * (total_games : ℕ) := by 
    exact_mod_cast eq2
  have eq4 : total_games = 27 := by
    omega
  exact_mod_cast eq4