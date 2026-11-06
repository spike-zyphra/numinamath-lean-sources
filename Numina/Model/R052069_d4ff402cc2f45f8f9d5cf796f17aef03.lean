import Mathlib

theorem inequalities_65475 (a b c : ℝ) (h₀ : a + b ≥ 0) (h₁ : b + c ≥ 0) (h₂ : c + a ≥ 0) :
    a + b + c ≥ (|a| + |b| + |c|) / 3 := by 
  cases' abs_cases a with ha ha
  · cases' abs_cases b with hb hb
    · cases' abs_cases c with hc hc
      · -- a ≥ 0, b ≥ 0, c ≥ 0
        linarith
      · -- a ≥ 0, b ≥ 0, c < 0
        linarith
    · cases' abs_cases c with hc hc
      · -- a ≥ 0, b < 0, c ≥ 0
        linarith
      · -- a ≥ 0, b < 0, c < 0
        linarith
  · cases' abs_cases b with hb hb
    · cases' abs_cases c with hc hc
      · -- a < 0, b ≥ 0, c ≥ 0
        linarith
      · -- a < 0, b ≥ 0, c < 0
        linarith
    · cases' abs_cases c with hc hc
      · -- a < 0, b < 0, c ≥ 0
        linarith
      · -- a < 0, b < 0, c < 0
        linarith