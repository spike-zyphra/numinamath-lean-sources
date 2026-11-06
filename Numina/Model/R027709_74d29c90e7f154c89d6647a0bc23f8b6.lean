import Mathlib

open Real

theorem number_theory_10678 {a b : ℕ → ℝ}
    (ha : ∀ n, a n = (2 + sqrt 7) ^ (2 * n + 1))
    (hb : ∀ n, b n = (a n) % 1) :
    ∀ n > 0, Odd (a n * b n) := by
  intro n hn
  use ( (a n * (b n) - 1) / 2 )
  simp [hb, ha, Odd]
  all_goals ring