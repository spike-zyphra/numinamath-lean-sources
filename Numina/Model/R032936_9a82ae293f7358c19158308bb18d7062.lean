import Mathlib

theorem algebra_134717 {a b c : ℤ} (ha : a ≠ 0) (t : ℝ)
    (h : a * t^2 + b * t + c = 0) :
    ∃ d e f : ℤ, d ≠ 0 ∧ d * (t + 2)^2 + e * (t + 2) + f = 0 := by
  use a
  use b - 4 * a
  use 4*a - 2*b + c
  constructor
  · -- Show that $a \neq 0$
    exact_mod_cast ha
  · -- Show that $t+2$ is a root of the new quadratic equation
    -- Substitute $t = (t+2) - 2$ into $h$ and simplify.
    -- The coefficients will be $a$, $b-4a$, $c+2b-4a$.
    have eq2 : (a : ℝ) * (t + 2)^2 + (b - 4*a : ℝ) * (t + 2) + (4*a - 2*b + c : ℝ) = (a : ℝ) * t^2 + (b : ℝ) * t + (c : ℝ) := by
      ring
    norm_num [Int.cast_add, Int.cast_sub, Int.cast_mul] at eq2 ⊢
    have eq3 : (a : ℝ) * (t + 2)^2 + (↑b - 4 * ↑a) * (t + 2) + (4 * ↑a - 2 * ↑b + ↑c) = (a : ℝ) * t^2 + (b : ℝ) * t + (c : ℝ) := by ring
    rw [eq3]
    exact_mod_cast h