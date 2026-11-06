import Mathlib
theorem inequalities_187774 {a b c : ℝ} (h1 : |a - b| ≥ |c|) (h2 : |b - c| ≥ |a|) (h3 : |c - a| ≥ |b|) : a = b + c ∨ b = a + c ∨ c = a + b:= by
  cases' abs_cases (a - b) with h11 h11 <;> 
  cases' abs_cases c with h12 h12 <;> 
  cases' abs_cases (b - c) with h21 h21 <;> 
  cases' abs_cases a with h22 h22 <;> 
  cases' abs_cases (c - a) with h31 h31 <;> 
  cases' abs_cases b with h32 h32 <;> 
    first
    | left; linarith
    | right; left; linarith
    | right; right; linarith