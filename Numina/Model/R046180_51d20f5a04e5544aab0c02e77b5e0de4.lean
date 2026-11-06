import Mathlib

theorem inequalities_71531 {a b c : ℝ} (h₀ : |a - b| ≥ |c|) (h₁ : |b - c| ≥ |a|)
    (h₂ : |c - a| ≥ |b|) :
    a = b + c ∨ b = c + a ∨ c = a + b := by 
  cases' abs_cases (a - b) with h h <;> 
  cases' abs_cases c with h' h' <;> 
  cases' abs_cases (b - c) with h'' h'' <;> 
  cases' abs_cases a with h''' h''' <;> 
  cases' abs_cases (c - a) with h'''' h'''' <;> 
  cases' abs_cases b with h''''' h''''' <;> 
    try { 
      first 
        | left; linarith 
        | right; left; linarith 
        | right; right; linarith 
    }