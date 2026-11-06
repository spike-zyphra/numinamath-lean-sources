import Mathlib

theorem algebra_225108 (x : ℤ) :
    ∃ n, x^2 + 3 * x + 24 = n^2 ↔ x = -23 ∨ x = -8 ∨ x = 5 ∨ x = 20 := by
  by_cases h1 : x ≤ 20
  · -- If x ≤ 20, then x must be one of the solutions
    by_cases h2 : x ≥ -23
    · -- x ∈ [-23, 20]
      have h3 : x ≤ 20 := h1
      have h4 : x ≥ -23 := h2
      interval_cases x <;> 
        try { 
          use 8
          all_goals 
            norm_num
        }
        <;> try { 
          use -8
          all_goals 
            norm_num
        }
        <;> try { 
          use 22
          all_goals 
            norm_num
        }
        <;> try { 
          use -22
          all_goals 
            norm_num
        }
    · -- x < -23
      use (x + 1)
      constructor
      · -- Assume x^2 + 3 * x + 24 = (x + 1)^2
        intro h
        nlinarith
      · -- Assume x = -23 ∨ x = -8 ∨ x = 5 ∨ x = 20
        intro h
        exfalso
        omega
  · -- If x > 20, then x must be one of the solutions (contradiction)
    have h1 : x > 20 := by 
      omega
    use (x + 1)
    constructor
    · -- Assume x^2 + 3 * x + 24 = (x + 1)^2
      intro h
      nlinarith
    · -- Assume x = -23 ∨ x = -8 ∨ x = 5 ∨ x = 20
      intro h
      exfalso
      omega