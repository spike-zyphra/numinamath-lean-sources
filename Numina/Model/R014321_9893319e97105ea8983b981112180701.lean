import Mathlib

theorem algebra_124784 (a b c : ℝ) (h₀ : abs (a - b) ≥ abs c) (h₁ : abs (b - c) ≥ abs a)
    (h₂ : abs (c - a) ≥ abs b) :
    a = b + c ∨ b = a + c ∨ c = a + b := by 
  cases' abs_cases (a - b) with h3 h3 <;> 
    cases' abs_cases c with h4 h4 <;> 
      cases' abs_cases (b - c) with h5 h5 <;> 
        cases' abs_cases a with h6 h6 <;> 
          cases' abs_cases (c - a) with h7 h7 <;> 
            cases' abs_cases b with h8 h8 <;> 
              try { 
              first
              | left; linarith
              | right; left; linarith
              | right; right; linarith
              }
  <;> try { 
    nlinarith 
  }