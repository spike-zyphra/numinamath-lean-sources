import Mathlib

theorem algebra_228768 (x y : ℝ) : abs (x + y) = abs x + abs y ↔ x * y ≥ 0 := by
  constructor
  · -- Forward: abs (x + y) = abs x + abs y implies x * y ≥ 0
    intro h
    cases' abs_cases (x + y) with h1 h1 <;> cases' abs_cases x with h2 h2 <;> cases' abs_cases y with h3 h3
    <;> try { nlinarith }
    <;> try { 
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]
    }
  · -- Backward: x * y ≥ 0 implies abs (x + y) = abs x + abs y
    intro h
    cases' abs_cases (x + y) with h1 h1 <;> cases' abs_cases x with h2 h2 <;> cases' abs_cases y with h3 h3
    <;> try { nlinarith }
    <;> try { 
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]
    }