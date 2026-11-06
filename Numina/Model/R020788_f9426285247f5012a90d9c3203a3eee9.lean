import Mathlib

theorem algebra_294231 {a b c : ℝ} (h : a + b + c = 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (ha : a ≠ 0) :
    a * (1 / b + 1 / c) + b * (1 / c + 1 / a) + c * (1 / a + 1 / b) + 3 = 0 := by

  have h1 : c = -a - b := by linarith 
  -- rewrite the expression into a single fraction.
  have eq1 : a * (1 / b + 1 / c) + b * (1 / c + 1 / a) + c * (1 / a + 1 / b) + 3 = 
      (a ^ 2 * (b + c) + b ^ 2 * (a + c) + c ^ 2 * (a + b) + 3 * (a * b * c)) / (a * b * c) := by
    have ha' : a ≠ 0 := ha
    have hb' : b ≠ 0 := hb
    have hc' : c ≠ 0 := hc
    field_simp
    ring
  -- substitute $c = -a - b$ into numerator.
  have h3 : a ^ 2 * (b + c) + b ^ 2 * (a + c) + c ^ 2 * (a + b) + 3 * (a * b * c) = 0 := by 
    -- Alternatively, without substitution, 
    -- by multiplying the original expression with abel and field_simp.
    -- Lean 4 can infer this.
    rw [show c = -a - b by linarith]
    nlinarith [sq_nonneg (a + b), sq_nonneg (a - b), sq_nonneg (a - b), sq_nonneg (a + b), sq_nonneg (a * b), sq_nonneg ((-a - b) * a), sq_nonneg ((-a - b) * b)]
  have h4 : a * b * c ≠ 0 := by
    apply mul_ne_zero
    apply mul_ne_zero
    exact ha
    exact hb
    exact hc
  rw [eq1]
  rw [h3]
  norm_num [h4]