import Mathlib

/- 14.3,29 ** Find a natural number $n$, such that each of $n, n+1, n+2, \cdots, n+20$ has a common divisor greater than 1 with $30030=2 \cdot 3 \cdot 5 \cdot 7 \cdot 11 \cdot 13$. -/
theorem number_theory_139175 (n : ℕ) (hn : n = 9440) :
    ∀ i ∈ Finset.Icc n (n + 20), Nat.gcd i 30030 > 1 := by
  subst n
  intro m hm
  simp at hm
  have : 9440 ≤ m := by tauto
  have : m ≤ 9460 := by tauto
  -- Check every number from 9440 to 9460 to see if it shares a common factor
  interval_cases m
  all_goals
    norm_num