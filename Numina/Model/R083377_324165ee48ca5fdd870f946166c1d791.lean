import Mathlib

open Nat

theorem number_theory_81521 {P : ℕ → ℕ}
    (hP : ∀ a, P a = sSup {x | Nat.Prime x ∧ x ∣ a ^ 2 + 1}) :
    ∀ n, ∃ a b c, a > n ∧ b > n ∧ c > n ∧ P a = P b ∧ P b = P c := by
  -- Let's think about how to solve this in Lean 4. We need to prove that given any natural number n, there exists a, b, c such that each is greater than n and such that all to evaluate to the same under $P$ where $P(a)$ is the largest prime divisor of $a^2 + 1$. We can choose the same number for a, b, c. In this case, $P(a) = P(b) = P(c)$ trivially, just by equality.

  intro n
  -- Let's think. If we have a, b, c all equal, then $P(a) = P(a)$ trivially. So we could choose all of them to be the same number, which is greater than each of them.

  use n + 1, n + 1, n + 1

  constructor
  · omega

  constructor
  · omega

  constructor
  · omega

  constructor
  · -- proves P a = P b
    rfl

  · -- proves P b = P c
    rfl