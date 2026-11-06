import Mathlib

open BigOperators

/- Theorem 6.6 states that for any positive integer \( n \), the sum of Euler's totient function \( \phi(d) \) over all positive divisors \( d \) of \( n \) is equal to \( n \). In mathematical terms, this can be expressed as:
$$\sum_{d \mid n} \phi(d) = n$$-/
theorem number_theory_4862 : ∀ (n : ℕ),
    ∑ m in Finset.filter (fun x => x ∣ n) (Finset.range (Nat.succ n)), Nat.totient m = n :=
  --The problem is exactly the proposition Nat.sum_totient' in Mathlib.
  Nat.sum_totient'
