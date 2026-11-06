import Mathlib

theorem inequalities_195338 (a b c : ℝ)
    (h₀ : |a - b| ≥ |c|) (h₁ : |b - c| ≥ |a|) (h₂ : |c - a| ≥ |b|) :
    a = b + c ∨ b = a + c ∨ c = a + b := by
  cases' abs_cases (a - b) with h h <;> 
  cases' abs_cases c with k k <;> 
  cases' abs_cases (b - c) with m m <;> 
  cases' abs_cases a with n n <;> 
  cases' abs_cases (c - a) with p p <;> 
  cases' abs_cases b with q q <;> 
    try { 
      first 
        | left; linarith 
        | right; left; linarith 
        | right; right; linarith 
    }
  all_goals 
    try { 
      exfalso <;> try { linarith }
    }