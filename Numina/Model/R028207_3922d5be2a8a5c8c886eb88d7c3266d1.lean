import Mathlib

theorem number_theory_154800 (n : ℕ) :
    ∑ k in Finset.Icc 0 n, (Nat.fib k)^2 = Nat.fib n * Nat.fib (n + 1) := by
  have h1 : ∀ n : ℕ, ∑ k in Finset.Icc 0 n, (Nat.fib k) ^ 2 = Nat.fib n * Nat.fib (n + 1) := by
    intro n 
    induction n with
    | zero =>
      simp [Finset.sum_singleton]
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [ih]
      simp [Nat.fib_add_two]
      <;> ring_nf <;> omega
  exact h1 n