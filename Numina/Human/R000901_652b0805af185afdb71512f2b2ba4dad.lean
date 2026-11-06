import Mathlib

open Complex

/- Given that both $i - 3$ and $b$ are roots of $ax^3 + 9x^2 + ax - 30,$ where $a$ and $b$ are real numbers, find $a + b.$ -/
theorem algebra_18965 {a b : ℝ} (h1 : a * (-3 + I) ^ 3 + 9 * (-3 + I) ^ 2 + a * (-3 + I) - 30 = 0)
    (h2 : a * b ^ 3 + 9 * b ^ 2 + a * b - 30 = 0) :
    a + b = 7 / 2 := by
  ring_nf at h1
  -- $a = 2$
  apply congrArg (fun x ↦ x.re) at h1
  rw [← two_add_one_eq_three, pow_add] at h1
  simp at h1
  have aeq : a = 2 := by
    linarith
  rw [aeq] at h2
  -- $b = 3 / 2$
  have eq : 2 * b ^ 3 + 9 * b ^ 2 + 2 * b - 30 = (2 * b - 3) * ((b + 3) ^ 2 + 1) := by 
    ring
  rw [eq] at h2
  rw [mul_eq_zero] at h2
  rcases h2 with h2 | h2
  linarith
  nlinarith