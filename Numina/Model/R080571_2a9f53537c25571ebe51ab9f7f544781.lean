import Mathlib

theorem number_theory_113965 (n : ℕ) :
    ∑ i in Finset.range (n + 1), Nat.fib i = Nat.fib (n + 2) - 1 := by
  induction n with
  | zero =>
    simp [Finset.sum_range_succ, Nat.fib]
    <;> try { rfl }
    <;> try { tauto }
  | succ n ih =>
    rw [Finset.sum_range_succ]
    rw [ih]
    simp [Nat.fib_add_two]
    all_goals
      try ring_nf
      <;> try { 
        cases n <;> simp [Nat.fib]
        <;> all_goals tauto 
      }
      <;> try omega