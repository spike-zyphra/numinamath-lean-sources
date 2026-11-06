import Mathlib

open Nat

/- Lemma 1: The tens digit of $n$ is equal to (n % 100) / 10 -/
theorem lemma_1 (n : ℕ) : (digits 10 n)[1]! = (n % 100) / 10 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  -- If n = 0, then the tens digit is 0
  . simp
  -- If n > 0, then the tens digit is equal to the ones digit of n / 10
  simp [hn]
  rcases Nat.eq_zero_or_pos (n / 10) with hn₁ | hn₁
  -- If n / 10 = 0, then its ones digit is 0
  . simp [hn₁]
    -- Also, n % 100 / 10 = 0 Since n < 10
    omega
  -- If n / 10 > 0, then the tens digit is equal to (n / 10) % 10
  . simp [hn₁]
    -- (n / 10) % 10 = (n % 100) / 10
    omega

/- Lemma 2: $n!$ is divisible by 100 for $n \ge 10$ -/
theorem lemma_2 {n : ℕ} (hn : 10 ≤ n) : 100 ∣ n ! := by
  -- Induction on n
  induction n, hn using le_induction with
  | base => decide -- Check 100 ∣ 10! = 3628800
  | succ n hn ih => exact Dvd.dvd.mul_left ih (n + 1) -- (n + 1)! = (n + 1) * n!, 100 ∣ n! → 100 ∣ (n + 1)!

/- Theorem: Let $M$ be a natural number such that $M \ge 9$. Let $S_M = \sum_{k=1}^{M} k!$. Show that the number of digits of $S_M$ when written in base 10 is greater than 1, and that the tens digit of $S_M$ is 1. -/
theorem number_theory_635663 (M : ℕ) (hM : 9 ≤ M) :
    (digits 10 (∑ k ∈ Finset.Icc 1 M, k !))[1]! = 1 := by
  -- We show that the tens digit of S_M is 1
  rw [lemma_1]
  -- We can show the stronger result that S_M % 100 = 13
  suffices (∑ k ∈ Finset.Icc 1 M, k !) % 100 = 13 by rw [this]
  -- Induction on M
  induction M, hM using le_induction with
  | base => decide -- ∑ k ∈ Finset.Icc 1 9, k ! = 409113
  | succ M hM ih =>
    -- Simplify using the lemma and the inductive hypothesis
    rw [Finset.sum_Icc_succ_top (by simp)]
    have ⟨s, hs⟩ : 100 ∣ (M + 1)! := lemma_2 (by omega)
    simpa [hs]