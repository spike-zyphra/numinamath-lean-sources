import Mathlib

theorem number_theory_324232 (n : ℕ) (h : n > 3) :
    ∃ x y, n = 2*x + 5*y := by 
        have h1 : n > 3 := h
        have h3 : n % 2 = 0 ∨ n % 2 = 1 := by omega
        rcases h3 with (h3 | h3)
        · 
          use n / 2
          use 0
          omega
        · 
          have h4 : n ≥ 5 := by 
            omega
          use (n - 5) / 2
          use 1
          omega