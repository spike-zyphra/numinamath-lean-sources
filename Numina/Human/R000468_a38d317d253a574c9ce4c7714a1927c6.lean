import Mathlib

/- The product of three even consecutive positive integers is twenty times their sum. What is the sum of the three integers? -/
theorem algebra_10993 {n : ℕ} (hn : Even n) (h : n * (n + 2) * (n + 4) = 20 * (n + (n + 2) + (n + 4))) :
    n + (n + 2) + (n + 4) = 24 := by
  rw [even_iff_two_dvd] at hn
  ring_nf at h
  nlinarith