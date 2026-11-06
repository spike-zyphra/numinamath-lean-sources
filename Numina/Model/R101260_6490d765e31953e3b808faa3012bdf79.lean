import Mathlib
open Real

theorem inequalities_2350 (x : ℝ) (hx : x > 0) :
    abs (4 - log x) ≥ 1 - (log x) ^ 2 ↔ x > 0 := by
  constructor
  · -- Assume abs (4 - log x) ≥ 1 - (log x) ^ 2, prove x > 0
    intro h
    exact hx
  · -- Assume x > 0, prove abs (4 - log x) ≥ 1 - (log x) ^ 2
    intro h
    by_cases h2 : 1 - (log x) ^ 2 ≥ 0
    · -- If 1 - (log x) ^ 2 ≥ 0, then we can work with the inequality by squaring both sides.
      have h3 : abs (4 - log x) ^ 2 ≥ (1 - (log x) ^ 2) ^ 2 := by
        cases abs_cases (4 - log x) with
        | inl h4 =>
          nlinarith [sq_nonneg (log x - 1), sq_nonneg (log x + 1)]
        | inr h4 =>
          nlinarith [sq_nonneg (log x - 1), sq_nonneg (log x + 1)]
      nlinarith [abs_nonneg (4 - log x), h2, h3, sq_nonneg (4 - log x), sq_nonneg (log x - 1), sq_nonneg (log x + 1)]
    · -- If 1 - (log x) ^ 2 < 0, the inequality is trivial because $|4 - \log x| \geq 0$.
      have h4 : (1 - (log x) ^ 2) < 0 := by linarith
      linarith [abs_nonneg (4 - log x), h4]