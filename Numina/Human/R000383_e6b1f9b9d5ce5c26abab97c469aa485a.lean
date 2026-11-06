import Mathlib

/- Given $f(x) = x^2 - 5x + 6$, find the solution set for the inequality $f(x) > 0$.-/
theorem algebra_9345 (f : ℝ → ℝ) (hf : f = fun x => x ^ 2 - 5 * x + 6) :
    {x | f x > 0} = {x | x > 3 ∨ x < 2} := by
  ext x
  -- From the given condition, we have $x^2 - 5x + 6 > 0$.
  simp [hf]
  -- Therefore, $(x-2)(x-3) > 0$.
  rw [show x^2-5*x+6 = (x-2)*(x-3) by ring, mul_pos_iff]
  -- This implies $x > 3$ or $x < 2$.
  apply or_congr
  . constructor
    . intros
      linarith
    intros
    constructor <;> linarith
  constructor
  . intros
    linarith
  intros
  constructor <;> linarith
