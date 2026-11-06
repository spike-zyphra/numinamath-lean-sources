import Mathlib

/- Three schools have a chess tournament. Four players come from each school. Each player plays three games against each player from the other schools, and plays one game against each other player from his or her own school. How many games of chess are played? -/
theorem algebra_18784 (n : ℕ) (hn : n = 3) : (n * 8 + n) * 12 / 2 = 162 := by
  rw [hn]