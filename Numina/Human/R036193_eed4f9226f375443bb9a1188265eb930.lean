import Mathlib

theorem algebra_83292 (f : ℝ × ℝ → ℝ)
    (hf1 : ∀ a b c : ℝ, a ≠ 0 → b ≠ 0 → c ≠ 0 → f (a, f (b, c)) = c * f (a, b))
    (hf2 : ∀ a : ℝ, a ≠ 0 → f (a, a) = 1)
    (x : ℝ) (hx : x ≠ 0) : 216 = f (x, 36) → x = 7776 := by
  -- Our goal is to show: x = 36 * f (x, 36)
  -- Then we substitute 216 = f (x, 36) into this, to obtain x = 7776.

  -- To show x = 36 * f (x, 36), we first need to show f (x, 1) = x.
  have fx1 : f (x, f (x, x)) = x * f (x, x) := hf1 x x x hx hx hx
  have fx2 : f (x, 1) = x := by
    rw [hf2 x hx] at fx1
    rw [mul_one] at fx1
    exact fx1

  -- We will need the fact that 36 ≠ 0 repeatedly.
  have nz_36 : (36 : ℝ) ≠ 0 := by linarith

  -- argument goes as follows:
  -- use a=x, b=36, c=36     => f(x, f(36,36)) = 36*f(x,36)
  -- replace f(36,36) with 1 => f(x,        1) = 36*f(x,36)
  -- replace f( x, 1) with x =>              x = 36*f(x,36)
  have fx3 : x = 36 * f (x, 36) := by
    have aux1 : f (x, f (36, 36)) = 36 * f (x, 36) := hf1 x 36 36 hx nz_36 nz_36
    have aux2 : f (x, 1) = 36 * f (x, 36) := by
      rw [hf2 36 nz_36] at aux1
      exact aux1
    rw [fx2] at aux2
    exact aux2

  -- We will use the above fact to solve the equation.
  intro fx36         -- assume 216 = f (x, 36)
  rw [← fx36] at fx3 -- substitute, so x = 36 * 216
  linarith           -- show x = 7776
