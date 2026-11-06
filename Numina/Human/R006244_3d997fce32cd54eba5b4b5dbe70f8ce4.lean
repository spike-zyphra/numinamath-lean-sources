import Mathlib

-- define the function N_L to count the number of leap years
def N_L (a b: ℕ) := ((Finset.Icc (a + 1) b).filter (fun n => (n % 4 = 0 ∧ n % 100 ≠ 0) ∨ n % 400 = 0)).card

/-Let Y0 be a given year. Assume that April 18 in year Y0 falls on a specific day of the week. Determine the soonest year
Y next strictly greater than Y0 such that April 18 in year Y next falls on the same day of the week.
The value of Y next is Y0 + k , where k is the smallest positive integer such that
(k + N_L(Y0, Y0+k))(mod7)=0. Here, N_L(Y0, Y0+k) is the number of leap years Y such that
Ya < Y < Yb. A year Y is defined as a leap year if it satisfies the conditions of the Gregorian calendar:
(Y is divisible by 4 AND Y is not divisible by 100) OR (Y is divisible by 400).
If Y0=2020, show that the answer is 2026-/

theorem number_theory_635104 (Y0: ℕ) (h: Y0 = 2020): IsLeast {k: ℕ | 0 < k ∧ (k + N_L Y0 (Y0 + k)) % 7 = 0} 6 := by
-- from the question, to show that Yk = 2026, it' is equivalent to show that the smallest k is 6

  constructor

  -- the forward direction
  .
    simp [h, N_L]
    native_decide

  -- the backward direction
  .
    intro k hk
    by_contra! l
    simp [h, N_L] at hk
    absurd hk
    interval_cases k
    all_goals native_decide