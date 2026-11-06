import Mathlib

theorem number_theory_246075 (n : ℕ) (h₀ : n > 2021) (h₁ : 5 ∣ n) (h₂ : 6 ∣ n)
    (h₃ : 1000 * (n % 100) + 100 * ((n / 100) % 100) = n + 3960) :
    n = 4080 := by 
  have h4 : n ≤ 4080 := by 
    omega 
  interval_cases n <;> omega