import Mathlib

/- Prove that there exist integers $a$, $b$, $c$ with $1 \le a < b < c \le 25$ and \[ S(a^6+2014) = S(b^6+2014) = S(c^6+2014) \] where $S(n)$ denotes the sum of the decimal digits of $n$.

[i]Proposed by Evan Chen[/i] -/
theorem number_theory_79098 :
    ∃ a b c : ℕ, 1 ≤ a ∧ a < b ∧ b < c ∧ c ≤ 25 ∧
      (Nat.digits 10 (a ^ 6 + 2014)).sum = (Nat.digits 10 (b ^ 6 + 2014)).sum ∧
      (Nat.digits 10 (b ^ 6 + 2014)).sum = (Nat.digits 10 (c ^ 6 + 2014)).sum := by
  use 1, 4, 10
  norm_num
  <;> decide