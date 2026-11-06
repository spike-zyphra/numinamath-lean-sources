import Mathlib

theorem number_theory_216942 {n : ℕ} (hn : Odd n ∧ 500 < n ∧ n < 1000) :
    (∑ d in n.divisors, d % 10) = 33 ↔ n = 729 := by
  rcases hn with ⟨hn_odd, hn1, hn2⟩
  interval_cases n <;> try { 
    native_decide
  }
  <;> try { contradiction }
  all_goals try { native_decide }