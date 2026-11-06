import Mathlib

/- Annie's soccer team is conducting a passing drill in which each of the 11 members of the soccer team must pass the ball to each of the other members exactly three times. How many times must the ball be passed before the passing drill is over? -/
theorem algebra_20394 (n : ℕ) (h : n = 11) :
    n * (n - 1) * 3 = 330 := by 
  subst h; rfl