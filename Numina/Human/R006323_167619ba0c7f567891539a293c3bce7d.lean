import Mathlib

/-Let $S$ be a positive integer.
Each morning of her five-day workweek,
Jane bought either a muffin at a cost of $50S$ cents or a bagel at a cost of $75S$ cents.
Her total cost for the week was a whole number of "S-dollars", where one S-dollar is equivalent to $100S$ cents.
Show that the number of bagels Jane bought is 2.-/

theorem number_theory_635875
  (M B S: ℕ) (hs: 0 < S) (h1: M + B = 5) (h2: 100 * S ∣ (50 * S * M + 75 * S * B)): B = 2 := by

  rw [show 50 * S * M + 75 * S * B = (25 * S) * (2 * M + 3 * B) by ring] at h2
  rw [show 100 * S = (25 * S) * 4 by ring] at h2
  have h3: 4 ∣ (2 * M + 3 * B) := by
    rw [Nat.mul_dvd_mul_iff_left] at h2
    tauto
    omega
  have lB: B ≤ 5 := by omega
  interval_cases B
  all_goals omega