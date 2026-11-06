import Mathlib
open Nat

/-
Prove that the sum of the reciprocals of the prime numbers diverges, i.e., show that:
\[
\sum_{i=1}^{\infty} \frac{1}{p_i} = \infty
\]
where $p_i$ denotes the $i$th prime number. Note: There is a proof using elementary tools.
-/
theorem number_theory_1857 (p : ℕ → ℕ) (hp₀ : p 1 = 2) (hp : ∀ n, p (n + 1) > p n)
    (hp' : ∀ n, Nat.Prime (p n)) :
    ¬ Summable fun i => (1 / p i : ℝ) := by
  have h1 : p 0 < 2 := by
    have h0 := hp 0
    have h1 := hp₀
    linarith
  have h2 : p 0 ≥ 2 := by
    have h0_prime : Nat.Prime (p 0) := hp' 0
    apply Nat.Prime.two_le at h0_prime
    linarith
  linarith [h1, h2]