import Mathlib

theorem number_theory_163660 {n : ℕ} (hn : n ∈ Finset.Icc 25 30) :
    2 * n = ∑ d in n.divisors, d ↔ n = 28 := by 
  rw [Finset.mem_Icc] at hn
  rcases hn with ⟨h1, h2⟩
  interval_cases n <;> try { native_decide }
  <;> try { contradiction }