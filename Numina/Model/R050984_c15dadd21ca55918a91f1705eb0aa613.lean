import Mathlib

theorem algebra_320794 (a b : ℝ) :
    (|a + b| - |a| + |b|) * (|a + b| - |a| - |b|) ≤ 0 := by
  cases' abs_cases (a + b) with hsum hsum
  all_goals cases' abs_cases a with ha ha
  all_goals cases' abs_cases b with hb hb
  all_goals 
    nlinarith [abs_nonneg (a + b), abs_nonneg a, abs_nonneg b]