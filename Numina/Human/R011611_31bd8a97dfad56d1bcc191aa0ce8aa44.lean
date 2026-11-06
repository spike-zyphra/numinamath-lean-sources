import Mathlib

open Real

/- ## Problem Statement

Find the derivative.
$$
y=\frac{3}{8 \sqrt{2}} \ln \frac{\sqrt{2}+\tanh x}{\sqrt{2}-\tanh x}-\frac{\tanh x}{4\left(2-\tanh^{2} x\right)}
$$
 -/
theorem calculus_138827 {f : ℝ → ℝ}
    (hf : f = λ x => (3 / (8 * sqrt 2)) * log ((sqrt 2 + tanh x) / (sqrt 2 - tanh x)) - tanh x / (4 * (2 - tanh x ^ 2))) :
    deriv f = λ x => 1 / (1 + cosh x ^ 2) ^ 2 := by
  ext x
  apply HasDerivAt.deriv
  -- Show that |tanh x| < 1 for all x.
  have abs_tanh_lt_one x : |tanh x| < 1 := by
    -- It is enough to consider the case 0 ≤ x since |tanh(-x)| = |-tanh(x)| = |tanh(x)|.
    wlog hx : 0 ≤ x generalizing x
    · have tanh_neg : tanh (-x) = -tanh x := by
        rw [tanh_eq_sinh_div_cosh, sinh_neg, cosh_neg, neg_div, tanh_eq_sinh_div_cosh]
      rw [← abs_neg, ← tanh_neg]
      apply this
      linarith
    -- The result follows from 0 ≤ sinh x < cosh x for x ≥ 0.
    rw [tanh_eq_sinh_div_cosh, abs_div, abs_of_pos (cosh_pos x), abs_of_nonneg (sinh_nonneg_iff.mpr hx)]
    rw [div_lt_iff₀ (cosh_pos x), one_mul]
    exact sinh_lt_cosh x
  have hsqrt2 : 1 < √2 := by
    rw [← sqrt_one]
    apply sqrt_lt_sqrt zero_le_one one_lt_two
  -- We have 0 < (√2 + tanh x) / (√2 - tanh x).
  have hineq1 : 0 < (√2 + tanh x) / (√2 - tanh x) := by
    have h := abs_tanh_lt_one x
    rw [abs_lt] at h
    apply div_pos <;> linarith
  -- We have (√2 + tanh x) / (√2 - tanh x) = (√2 * cosh x + sinh x) / (√2 * cosh x - sinh x).
  have eq1 x : (√2 + tanh x) / (√2 - tanh x) = (√2 * cosh x + sinh x) / (√2 * cosh x - sinh x) := by
    rw [tanh_eq_sinh_div_cosh]
    field_simp
  -- We have tanh x / (4 * (2 - tanh x ^ 2)) = (1 / 4) * (sinh x * cosh x / (1 + cosh x^2))
  -- (because 1 = cosh x^2 - sinh x^2).
  have eq2 x : tanh x / (4 * (2 - tanh x ^ 2)) = (1 / 4) * (sinh x * cosh x / (1 + cosh x^2)) := by
    have h := abs_tanh_lt_one x
    rw [abs_lt] at h
    field_simp [show (2 - tanh x ^ 2) ≠ 0 by nlinarith]
    rw [tanh_eq_sinh_div_cosh]
    field_simp
    nth_rw 1 [← cosh_sq_sub_sinh_sq x]
    ring
  simp_rw [hf, eq1, eq2]
  clear hf eq2
  -- Define a, b, c, d as linear combinations of sinh(x) and cosh(x) which
  -- appear in the goal expression.
  set a := √2 * sinh x + cosh x
  set b := √2 * cosh x - sinh x
  set c := √2 * cosh x + sinh x
  set d := √2 * sinh x - cosh x
  -- We have 0 < b since sinh(x) < cosh(x), 1 < √2, and 0 < cosh x.
  have hb : 0 < b := by
    rw [sub_pos, ← one_mul (sinh x)]
    apply mul_lt_mul_of_le_of_lt_of_pos_of_nonneg <;> linarith [sinh_lt_cosh x, cosh_pos x]
  -- It is enough to show that the derivative is equal to
  -- 1 / (1 + cosh x ^ 2) ^ 2 = 3 / (8 * √2) * (((a * b - c * d) / b^2) / (c / b))
  --  - 1 / 4 * (((cosh x * cosh x + sinh x * sinh x) * (1 + cosh x^2) - sinh x * cosh x * (2 * cosh x * sinh x)) / (1 + cosh x^2)^2)
  suffices 1 / (1 + cosh x ^ 2) ^ 2 = 3 / (8 * √2) * (((a * b - c * d) / b^2) / (c / b))
      - 1 / 4 * (((cosh x * cosh x + sinh x * sinh x) * (1 + cosh x^2) - sinh x * cosh x * (2 * cosh x * sinh x)) / (1 + cosh x^2)^2) by
    -- This result follows from basic properties of derivatives.
    rw [this]; clear this
    apply HasDerivAt.sub
    · apply HasDerivAt.const_mul
      apply HasDerivAt.log
      · apply HasDerivAt.div
        · apply HasDerivAt.add
          · apply HasDerivAt.const_mul
            exact hasDerivAt_cosh x
          · exact hasDerivAt_sinh x
        · apply HasDerivAt.sub
          · apply HasDerivAt.const_mul
            exact hasDerivAt_cosh x
          · exact hasDerivAt_sinh x
        · exact ne_of_gt hb
      · rw [← eq1]
        linarith
    · apply HasDerivAt.const_mul
      apply HasDerivAt.div
      · apply HasDerivAt.mul (hasDerivAt_sinh x) (hasDerivAt_cosh x)
      · apply HasDerivAt.const_add
        rw [show 2 * cosh x * sinh x = 2 * cosh x ^ 1 * sinh x by ring]
        apply HasDerivAt.pow _ (hasDerivAt_cosh x)
      · positivity
  clear eq1 hineq1
  -- Show that (a * b - c * d) / b^2 / (c / b) = (a * b - c * d) / (b * c).
  have eq1 : (a * b - c * d) / b ^ 2 / (c / b) = (a * b - c * d) / (b * c) := by
    rw [div_div, pow_two]
    congr 1
    rw [mul_assoc, mul_div_cancel₀ _ (by linarith)]
  -- Show that a * b = sinh (2 * x) / 2 + √2.
  have eq2 : a * b = sinh (2 * x) / 2 + √2 := by
    simp [a, b, sinh_two_mul]
    ring_nf
    rw [sq_sqrt zero_le_two]
    linear_combination √2 * (cosh_sq_sub_sinh_sq x)
  -- Show that c * d = sinh (2 * x) / 2 - √2.
  have eq3 : c * d = sinh (2 * x) / 2 - √2 := by
    simp [c, d, sinh_two_mul]
    ring_nf
    rw [sq_sqrt zero_le_two]
    linear_combination -√2 * (cosh_sq_sub_sinh_sq x)
  -- Show that b * c = 1 + cosh x^2.
  have eq4 : b * c = 1 + cosh x^2 := by
    simp [a, b]
    ring_nf
    rw [sq_sqrt zero_le_two]
    linear_combination (cosh_sq_sub_sinh_sq x)
  -- Show that (cosh x * cosh x + sinh x * sinh x) * (1 + cosh x ^ 2) - sinh x * cosh x * (2 * cosh x * sinh x) = 3 * sinh x ^ 2 + 2.
  have eq5 : (cosh x * cosh x + sinh x * sinh x) * (1 + cosh x ^ 2) - sinh x * cosh x * (2 * cosh x * sinh x) = 3 * sinh x ^ 2 + 2 := by
    ring_nf
    rw [sinh_sq]
    ring
  -- Use eq1, eq2, eq3, eq4, and eq5 to simplify the expression.
  rw [eq1, eq2, eq3, eq4, eq5]
  rw [show ∀ a b : ℝ, a + b - (a - b) = 2 * b by intros; ring]
  have eq6 a : 3 / (8 * √2) * (2 * √2 / a) = 3 / (4 * a) := by
    rw [show 3 / (8 * √2) * (2 * √2 / a) = (3 * √2) / ((4 * a) * √2) by ring]
    rw [mul_div_mul_right _ _ (by positivity)]
  rw [eq6]
  have eq7 {a d : ℝ} (hd : d ≠ 0) : 3 / (4 * d) - 1 / 4 * (a / d^2) = (3 * d - a) / (4 * d^2) := by
    field_simp
    ring
  rw [eq7 (by positivity)]
  -- It is left to show that 3 * (1 + cosh x ^ 2) - (3 * sinh x ^ 2 + 2) = 4.
  suffices 3 * (1 + cosh x ^ 2) - (3 * sinh x ^ 2 + 2) = 4 by
    rw [this]
    field_simp
  linear_combination 3 * (cosh_sq_sub_sinh_sq x)