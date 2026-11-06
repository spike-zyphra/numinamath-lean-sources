import Mathlib

theorem algebra_268696 (total_songs : ℕ) (h : total_songs ≠ 0)
    (h1 : (40 / 100 : ℝ) * total_songs = (35 / 100 : ℝ) * total_songs + (15 / 100 : ℝ) * total_songs) :
    (15 / 100 : ℝ) * total_songs = 39 := by
  have h2 : (total_songs : ℝ) = 0 := by
    linarith
  have h3 : total_songs = 0 := by
    exact_mod_cast h2
  contradiction