import Mathlib
open Real

theorem algebra_2239 {a b : ℝ} : |a - b| = |a| + |b| ↔ a * b ≤ 0 := by
  constructor
  · -- Forward direction: |a - b| = |a| + |b| implies a * b ≤ 0
    intro h
    cases' abs_cases (a - b) with h1 h1 <;> 
      cases' abs_cases a with h2 h2 <;> 
        cases' abs_cases b with h3 h3 <;> 
          nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a), sq_nonneg (b)]
  · -- Backward direction: a * b ≤ 0 implies |a - b| = |a| + |b|
    intro h
    cases' abs_cases (a - b) with h1 h1 <;> 
      cases' abs_cases a with h2 h2 <;> 
        cases' abs_cases b with h3 h3 <;> 
          nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a), sq_nonneg (b), h]