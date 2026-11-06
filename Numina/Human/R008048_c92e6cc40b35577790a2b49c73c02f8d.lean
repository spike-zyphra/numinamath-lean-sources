import Mathlib

/- At Beaumont High School, there are 12 players on the baseball team.  All 12 players are taking at least one of biology or chemistry.  If 7 players are taking biology and 2 players are taking both sciences, how many players are taking chemistry? -/
theorem algebra_13265 (total_players : ℕ) (h : total_players = 12) (taking_biology : ℕ) (h_biology : taking_biology = 7) (taking_both : ℕ) (h_both : taking_both = 2) :
    total_players - taking_biology + taking_both = 7 := by
  rw [h, h_biology, h_both]
