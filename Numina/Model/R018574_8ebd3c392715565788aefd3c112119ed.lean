import Mathlib

theorem number_theory_110544 (n : ℕ) (hn : n > 0) (x : ℤ) :
    ∃ k : ℤ, (x^(5*n) + 2*x^(2*n) - x^n + 1)/(x^(5*n) + x^n - 1) = k ↔
    x = 0 ∨ x = -1 ∨ x = 1 := by
  by_cases h : x = 0 ∨ x = -1 ∨ x = 1
  · -- Assume x is either 0, -1 or 1. Then the equivalence holds with k being the value of the fraction.
    use (x^(5*n) + 2*x^(2*n) - x^n + 1)/(x^(5*n) + x^n - 1)
    simp [h]
    all_goals
      try { tauto }
  · -- Assume x is not 0, -1 or 1, then we need to choose k such that equality is false
    have hx0 : x ≠ 0 := by
      intro h0
      have : x = 0 := by
        omega
      tauto
    have hx1 : x ≠ -1 := by
      intro h1
      have : x = -1 := by
        omega
      tauto
    have hx2 : x ≠ 1 := by
      intro h2
      have : x = 1 := by
        omega
      tauto
    use ( (x^(5*n) + 2*x^(2*n) - x^n + 1)/(x^(5*n) + x^n - 1) + 1 )
    simp [show ¬(x = 0) by tauto, show ¬(x = -1) by tauto, show ¬(x = 1) by tauto]
    all_goals
      try { tauto }
      all_goals
        try { 
          omega 
        }