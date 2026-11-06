import Mathlib

theorem number_theory_186864 (n : ℕ) (hn : n > 500 ∧ n < 1000 ∧ Odd n) :
    (∑ d in n.divisors, (d % 10)) = 33 ↔ n = 729 := by
  rcases hn with ⟨h1, h2, h3⟩
  interval_cases n <;> try { 
    native_decide 
  }
  <;> try { 
    contradiction 
  }
  <;> try { 
    trivial 
  }
  <;> omega