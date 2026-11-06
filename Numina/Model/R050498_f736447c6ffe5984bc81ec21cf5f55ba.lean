import Mathlib

theorem algebra_275954 {a b c : ℝ} : (a + b + c)^3 + (b - a - c)^3 + (c - a - b)^3 +
    (a - b - c)^3 = 24 * a * b * c := by
  ring  --ring tactic is powerful enough to prove polynomial identities