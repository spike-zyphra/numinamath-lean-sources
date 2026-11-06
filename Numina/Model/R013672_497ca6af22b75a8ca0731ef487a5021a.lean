import Mathlib

theorem number_theory_252594 (a b : ℤ) (n : ℕ) (hn : n > 0) :
    ∃ k : ℤ, (b^(n - 1) * ∏ i ∈ Finset.range n, (a + (i * b))) / Nat.factorial n = k := by
  refine' ⟨(b^(n - 1) * ∏ i ∈ Finset.range n, (a + (i * b))) / Nat.factorial n, rfl⟩