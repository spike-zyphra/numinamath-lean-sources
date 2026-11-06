import Mathlib

theorem inequalities_2091 (x : ℝ) (h : abs (x + 1) > abs (x + 4)) : x < -5 / 2 := by
  cases abs_cases (x + 1) with
  | inl h1 =>
    cases abs_cases (x + 4) with
    | inl h2 =>
      linarith
    | inr h2 =>
      linarith
  | inr h1 =>
    cases abs_cases (x + 4) with
    | inl h2 =>
      linarith
    | inr h2 =>
      linarith