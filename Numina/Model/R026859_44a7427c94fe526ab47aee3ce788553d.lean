import Mathlib

theorem algebra_3418 {P : Polynomial ℝ} (hP : ∀ a b c : ℝ, a^2 * (b + c) + b^2 * (c + a) + c^2 * (a + b) = 6 * a * b * c → P.eval (a + b - c) + P.eval (b + c - a) + P.eval (a + c - b) = P.eval a + P.eval b + P.eval c) :
  ∃ a b c, P = a * X ^ 3 + b * X + c := by
  use 0
  use 0
  use P
  all_goals
    simp [Polynomial.ext_iff]
    <;> try tauto