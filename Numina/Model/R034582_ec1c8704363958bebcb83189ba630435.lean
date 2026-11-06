import Mathlib

theorem number_theory_297399 (n : ℕ) (h₀ : n % 10 = (n / 10) % 10 - 3)
    (h₁ : (1000 * (n % 10) + 100 * ((n / 10) % 10) +
      10 * ((n / 100) % 10) + (n / 1000)) - n = 8987) :
    n = 1996 := by 
  omega