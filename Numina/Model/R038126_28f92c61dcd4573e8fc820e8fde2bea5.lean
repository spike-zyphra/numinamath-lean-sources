import Mathlib

theorem number_theory_187862 (n : ℕ) :
    ∑ i in Finset.range n, Nat.fib (i + 1) = Nat.fib (n + 2) - 1 := by
  have h1 : ∀ (n : ℕ), ∑ i in Finset.range n, Nat.fib (i + 1) = Nat.fib (n + 2) - 1 := by
    intro n
    induction n with
    | zero =>
      simp [Finset.sum_range_zero, Nat.fib]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      cases n with
      | zero =>
        simp [Nat.fib]
        <;> omega
      | succ n =>
        simp [Nat.fib_add_two, Nat.add_assoc] at *
        <;> omega
  specialize h1 n
  exact h1