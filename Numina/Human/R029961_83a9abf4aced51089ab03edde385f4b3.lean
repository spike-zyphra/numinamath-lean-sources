import Mathlib

/- Theorem 6.3 states that for a prime number \( p \) and a positive integer \( a \), the Euler's totient function evaluated at \( p^a \) is given by the formula \( \phi(p^a) = p^a - p^{a-1} = p^{a-1}(p - 1) \).-/
theorem number_theorey_4859 (p a : ℕ) [hp : Fact (Nat.Prime p)] (ha : 1 ≤ a):
    (p ^ a).totient = p ^ a - p ^ (a - 1) := by
  --The problem is exactly the proposition Nat.totient_prime_pow in Mathlib.
  rw [Nat.totient_prime_pow, Nat.mul_sub_left_distrib]
  nth_rw 2 [← Nat.pow_one p]; rw [← Nat.pow_add, ← Nat.sub_add_comm]
  simp; exact ha; exact hp.1; linarith
