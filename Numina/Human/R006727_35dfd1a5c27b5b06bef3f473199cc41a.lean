import Mathlib

/- Let $M$ be an integer such that $1 \le M \le 9$. Show that there exists a natural number $n$ such that the sum of the base-10 digits of $n^2$ is $M^2$. -/
theorem number_theory_640587
  (M : ℕ)
  (hM : 1 ≤ M ∧ M ≤ 9)
  : ∃ n : ℕ, (Nat.digits 10 (n^2)).sum = M^2 :=
by
  use Nat.ofDigits 10 (List.replicate M 1)
  cases hM
  interval_cases M
  simp
  all_goals
    simp [Nat.ofDigits, Nat.digits, Nat.digitsAux]
