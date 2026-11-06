import Mathlib

theorem algebra_256698 (f : ℝ → ℝ) (hf : f = fun x => 2007 * x^3 + 2006 * x^2 + 2005 * x) :
    ∃! x, f x = 0 := by 
  use 0
  constructor
  · -- Show that 0 is indeed a root 
    simp [hf]
  · -- Show that 0 is the unique root 
    intro x hx 
    simp [hf] at hx 
    -- We need to show that from $2007 x^3 + 2006 x^2 + 2005 x = 0$, it follows that x = 0
    -- Factor the equation: x(2007 x^2 + 2006 x + 2005) = 0.
    -- Since the quadratic has no real roots (as its discriminant is negative), x = 0 is the only solution.
    have h_eq : x * (2007 * x ^ 2 + 2006 * x + 2005) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h_eq) with h1 h2
    · -- Case where x = 0 
      linarith 
    · -- Case where 2007 * x^2 + 2006 * x + 2005 = 0
      nlinarith [sq_nonneg (2007 * x + 1003), sq_nonneg (x + 1003 / 2007), sq_nonneg (x + 1003 / 2007 - 2 * 2007 / 2007), sq_nonneg (x * 2007), sq_nonneg ((2007 * x + 1003) * 2007), sq_nonneg ((x * 2007 + 1003) * 2007)]