import Mathlib

theorem algebra_195542 {n : ℕ} (hn : n > 0) (h : n * (n + 1) = n + 52) :
    n * (n + 1) = 108 := by
  have h1 : n ≤ 7 := by
    nlinarith
    all_goals nlinarith 
  interval_cases n <;> omega
  all_goals omega