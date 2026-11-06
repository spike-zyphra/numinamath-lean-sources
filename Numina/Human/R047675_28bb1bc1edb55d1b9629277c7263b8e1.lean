import Mathlib

/- Suppose $a$, $b$, and $c$ are positive real numbers, and $a+b+c=9$, then the minimum value of $\frac{2}{a}+\frac{2}{b}+\frac{2}{c}$ is $\_\_\_\_\_\_\_\_\_.$ -/
theorem algebra_9090_1 : ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a + b + c = 9 ∧ 2 / a + 2 / b + 2 / c = 2 := by
  -- Note that I break the problem into two:
  -- 1. There exists a, b, c such that a + b + c = 9 and 2 / a + 2 / b + 2 / c = 2
  -- 2. For any a, b, c such that a + b + c = 9, 2 / a + 2 / b + 2 / c ≥ 2
  -- The first part is trivial by setting a = b = c = 3
  use 3, 3, 3
  norm_num

/- For any a, b, c such that a + b + c = 9, 2 / a + 2 / b + 2 / c ≥ 2 -/
theorem algebra_9090_2 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = 9) :
    2 / a + 2 / b + 2 / c ≥ 2 := by

  -- Lemma : For any x, y > 0, x / y + y / x ≥ 2
  have l {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : x / y + y / x ≥ 2 := by
    -- Multiply both sides by xy
    refine le_of_mul_le_mul_of_pos_right ?_ hx
    refine le_of_mul_le_mul_of_pos_right ?_ hy

    apply ne_of_gt at hx
    apply ne_of_gt at hy
    field_simp

    -- Simplify the goal by eliminating the denominator
    have : (x * x + y * y) * x * y / (y * x) = x * x + y * y := by
      simp [div_eq_mul_inv]
      field_simp
      ring
    rw [this]

    -- Equivalent to (x-y)^2 ≥ 0
    linarith [sq_nonneg (x - y)]

  -- Multiply a + b + c to RHS and 9 to LHS
  refine le_of_mul_le_mul_of_pos_right ?_ (by norm_num : 9 > (0 : ℝ))
  nth_rewrite 2 [←h]

  -- Transform RHS to the form of the lemma
  have ka := mul_inv_cancel₀ (ne_of_gt ha)
  have kb := mul_inv_cancel₀ (ne_of_gt hb)
  have kc := mul_inv_cancel₀ (ne_of_gt hc)
  have : (2 / a + 2 / b + 2 / c) * (a + b + c) = 2 * (3 + a / b + b / a + c / a + a / c + b / c + c / b) := by
    simp [div_eq_mul_inv]
    linarith
  rw [this]

  -- Apply the lemma
  linarith [l ha hb, l hb hc, l hc ha]
