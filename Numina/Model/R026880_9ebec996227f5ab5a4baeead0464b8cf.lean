import Mathlib

theorem number_theory_159140 (n : ℕ) (h₀ : n < 10000) (h₁ : n + (n % 10) = 5574)
    (h₂ : n + ((n / 10) % 10) = 557) :
    n = 5567 := by 
  have h3 : n ≤ 5574 := by
    omega
  have h4 : n < 5575 := by
    omega
  interval_cases n <;> omega