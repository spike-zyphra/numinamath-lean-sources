import Mathlib

/- Solve for $x,$ where
\[\frac{x}{x - a} + \frac{x - b}{x - a - b} = \frac{x - a}{x - 2a} + \frac{x + a - b}{x - b}.\]Assume that $2a > x > b > a > 0.$ -/
theorem algebra_21517 {x a b : ℝ} (ha : 0 < a) (hb : a < b) (hc : b < x)
    (hd : x < 2 * a) (h : x / (x - a) + (x - b) / (x - a - b) =
    (x - a) / (x - 2 * a) + (x + a - b) / (x - b)) :
    x = (2 * a + b) / 2 := by
  -- $x - a \neq 0$
  have xsubane : x - a ≠ 0 := by
    linarith
  -- $x - b \neq 0$
  have xsubbne : x - b ≠ 0 := by
    linarith
  -- $x - 2a \neq 0$
  have xsub2ane : x - 2 * a ≠ 0 := by
    linarith
  -- $x - a - b \neq 0$
  have xsubabne : x - a - b ≠ 0 := by
    linarith
  -- $(x(x - a) + (x - b)(x - a - b))((x - 2a)(x - b)) = ((x - a)(x - b) + (x + a - b)(x - 2a))((x - a)(x - a - b))$
  field_simp at h
  -- $(x(x - a) + (x - b)(x - a - b))((x - 2a)(x - b)) - ((x - a)(x - b) - (x + a - b)(x - 2a))((x - a)(x - a - b)) = 0$
  apply sub_eq_zero_of_eq at h
  -- $(x(x - a - b) + (x - b)(x - a))((x - 2a)(x - b)) - ((x - a)(x - b) + (x + a - b)(x - 2a))((x - a)(x - a - b)) = a^2(2x - 2a - b)(b - a)$
  have eq : (x * (x - a - b) + (x - b) * (x - a)) * ((x - 2 * a) * (x - b)) - ((x - a) * (x - b) + (x + a - b) * (x - 2 * a)) * ((x - a) * (x - a - b)) = a ^ 2 * (2 * x - 2 * a - b) * (b - a) := by
    ring_nf
  -- So $a^2(2x - 2a - b)(b - a) = 0$
  rw [h] at eq
  -- So $a = 0$ or $2x - 2a - b = 0$ or $b - a = 0$
  simp only [zero_eq_mul, mul_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff] at eq
  -- So $x = (2a + b) / 2$
  rcases eq with ⟨eq | eq⟩ | eq
  any_goals
  linarith