import Mathlib

theorem number_theory_7857 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) : (Nat.fib m).gcd (Nat.fib n) = Nat.fib (m.gcd n) := by 
  have h1 : (Nat.fib m).gcd (Nat.fib n) = Nat.fib (m.gcd n) := by
    rw [Nat.fib_gcd]
    all_goals
      try { 
        simp_all [Nat.fib_pos]
        <;> try { 
          tauto
        }
      }
  exact h1