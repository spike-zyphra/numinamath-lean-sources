import Mathlib

/- Show by mathematical induction that if \( n \) is a positive integer, then \( (2n)! < 2^{2n} (n!)^2 \).-/
theorem number_theory_4550 (n : ℕ) (hn : 0 < n) :
    (Nat.factorial (2*n)) < 2^(2*n) * Nat.factorial n^2 := by
  cases n
  linarith
  rename_i n
  induction n
  -- First, we check the base case when \( n = 1 \):
  simp
  -- Now, we assume that the statement is true for some positive integer \( k \), i.e., we assume:
  rename_i n ht
  -- We need to show that the statement is also true for \( k + 1 \), i.e., we need to prove: (2(k+1))! < 2^{2(k+1)} ((k+1)!)^2
  have h1: 2 * (Nat.succ n + 1) = 2 * (n + 1) + 1 + 1 := by linarith
  --We can express \( (2(k+1))! \) as: (2(k+1))! = (2k + 2)! = (2k + 2)(2k + 1)(2k)!
  rw [h1,Nat.factorial_succ,Nat.factorial_succ]
  rw [Nat.pow_succ,Nat.pow_succ]
  rw [Nat.factorial_succ]
  have h2:(2 * (n + 1) + 1 + 1) * ((2 * (n + 1) + 1) * Nat.factorial (2 * (n + 1))) =
    Nat.factorial (2 * (n + 1)) * ((2*n+4)*(2*n+3)) := by ring
  rw [h2]
  have h3:2 ^ (2 * (n + 1)) * 2 * 2 * ((n + 1 + 1) * Nat.factorial (n + 1)) ^ 2 = (2 ^ (2 * (n + 1)) * Nat.factorial (n + 1) ^ 2) * (4*(n + 2)^2) := by ring
  rw [h3]
  -- apply the induction hypothesis
  apply mul_lt_mul
  apply ht
  linarith
  nlinarith
  positivity
  positivity
