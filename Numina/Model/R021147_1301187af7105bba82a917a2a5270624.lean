import Mathlib

theorem algebra_197244 (n m : ℕ) (h₀ : n ∈ Finset.Icc 10 99) (h₁ : m ∈ Finset.Icc 10 99)
    (h₂ : (10 * (m % 10) + (m / 10)) * n = n * m + 3816) :
    n * m = 1007 := by
  rw [Finset.mem_Icc] at h₀ h₁
  rcases h₀ with ⟨hn1, hn2⟩
  rcases h₁ with ⟨hm1, hm2⟩
  interval_cases n <;> try { 
    omega 
  } <;> try { 
    interval_cases m <;> omega 
  }