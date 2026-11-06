import Mathlib

theorem number_theory_139207 (n : ℕ) (h₀ : n > 0) (h₁ : n ≤ 2005 - 17) :
    ∃ m ∈ Finset.Icc n (n + 17), (Nat.digits 10 m).sum ∣ m := by
  have h3 : n > 0 := h₀
  have h4 : n ≤ 2005 - 17 := h₁
  have h5 : n ≤ 1988 := by
    omega
  interval_cases n <;> try { 
    native_decide
  }
  <;> try { 
    omega 
  }