import Mathlib

open Real Set

theorem inequalities_62625 (a b c : ℝ) (h : abs (a + b) + abs (b + c) + abs (c + a) = 8) :
    a ^ 2 + b ^ 2 + c ^ 2 ≤ 48 ∧ a ^ 2 + b ^ 2 + c ^ 2 ≥ 16 / 3 := by 
  constructor
  · -- Prove that $a^2 + b^2 + c^2 \leq 48$
    cases' abs_cases (a + b) with h1 h1 <;> 
    cases' abs_cases (b + c) with h2 h2 <;> 
    cases' abs_cases (c + a) with h3 h3 <;> 
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
  · -- Prove that $a^2 + b^2 + c^2 \geq 16/3$
    cases' abs_cases (a + b) with h1 h1 <;> 
    cases' abs_cases (b + c) with h2 h2 <;> 
    cases' abs_cases (c + a) with h3 h3 <;> 
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]