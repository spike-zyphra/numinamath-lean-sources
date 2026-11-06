import Mathlib

/- Solve the equation: $\frac{4}{{{x^2}+x}}-\frac{3}{{{x^2}-x}}=0$.-/
theorem algebra_9189 (x : ℝ) (hx1 : x ^ 2 + x ≠ 0) (hx2 : x ^ 2 - x ≠ 0) :
    4 / (x ^ 2 + x) - 3 / (x ^ 2 - x) = 0 ↔ x = 7 := by
  constructor
  swap
  -- Verify that x=7 is solution.
  . intro h
    subst h
    norm_num
  -- Notice that x,x+1,x-1 are not zero.
  have : x ≠ 0 := fun h => by norm_num [h] at hx1
  have : x + 1 ≠ 0 := fun h => by
    have : x = -1 := by linarith
    norm_num [this] at hx1
  have : x - 1 ≠ 0 := fun h => by
    have : x = 1 := by linarith
    norm_num [this] at hx2
  intro h
  -- We can cancel denominator by multiplying x(x+1)(x-1) at both side of above equation.
  rw [show x ^ 2 + x = x * (x + 1) by ring, show x ^ 2 - x = x * (x - 1) by ring] at h
  field_simp at h
  -- It's clear that x=7 is the only solution.
  have : x * (x - 7) = 0 := by linear_combination h
  rw [mul_eq_zero] at this
  exact this.elim (fun h => by contradiction) (fun h => by linear_combination h)
