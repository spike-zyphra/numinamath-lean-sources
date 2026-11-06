import Mathlib

/- Of the students attending a school party, $60\%$ of the students are girls, and $40\%$ of the students like to dance. After these students are joined by $20$ more boy students, all of whom like to dance, the party is now $58\%$ girls. How many students now at the party like to dance?-/
theorem algebra_734 (t: ℚ) (p: g = 60/100 * t) (q: g = 58/100 * (t + 20)): 40 / 100 * t + 20 = 252 := by
  linarith