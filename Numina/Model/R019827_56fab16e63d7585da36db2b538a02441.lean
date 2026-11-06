import Mathlib

theorem number_theory_168937 (n : ℕ) (h₀ : 1 ≤ n) (h₁ : n + 50 ≤ 100) :
    ∃ m ∈ Finset.Icc n (n + 50), ∃ p ∈ Finset.Icc n (n + 50), m ≠ p ∧ m = 2 * p := by
  have h2 : n ≤ 50 := by 
    omega
  interval_cases n <;> try { 
    native_decide 
  }
  <;> try { 
    all_goals
    try { 
      native_decide 
    }
    all_goals
    try { 
      omega 
    }
    all_goals
    try { 
      aesop 
    }
  }