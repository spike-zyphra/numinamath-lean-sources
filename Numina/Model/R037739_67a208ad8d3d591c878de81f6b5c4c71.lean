import Mathlib

theorem number_theory_29490 (n : ℕ) (hn : n ∈ Finset.Icc 2 15) (h : n.divisors.card = 6) :
    n = 12 := by
  rw [Finset.mem_Icc] at hn
  rcases hn with ⟨hn2, hn15⟩
  interval_cases n <;> try { contradiction }
  <;> try { trivial }
  <;> try { native_decide }