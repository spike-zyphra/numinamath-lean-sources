import Mathlib

theorem number_theory_223492 (n : ℕ) (h₀ : n > 0) :
    35 ∣ ∑ i ∈ Finset.range 35, (n + i)^2 := by
  have h1 : ∀ n : ℕ, 35 ∣ ∑ i in Finset.range 35, (n + i) ^ 2 := by
    intro n
    simp only [Finset.sum_range_succ]
    ring_nf
    omega
  specialize h1 n
  simpa using h1