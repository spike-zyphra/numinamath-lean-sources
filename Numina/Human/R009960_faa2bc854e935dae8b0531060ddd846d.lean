import Mathlib

/- The 450 juniors at East HS drink a total of 1500 cartons of milk per 5-day week. If the average senior drinks milk at the same rate as the average junior, what is the average number of total cartons of milk the 600 seniors drink each school day? -/
theorem algebra_21591 (j s : ℕ) (hj : j = 450) (hs : s = 600)
    (h : 5 * j * x = 1500) :
    s * x = 400 := by
  subst hj; subst hs
  omega