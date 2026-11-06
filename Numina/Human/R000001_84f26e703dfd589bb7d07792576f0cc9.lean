import Mathlib

/- Given that the product \( a \cdot b \cdot c = 1 \), what is the value of the following expression?
$$
\frac{a}{a b + a + 1} + \frac{b}{b c + b + 1} + \frac{c}{c a + c + 1}
$$-/
theorem algebra_4013 {a b c : ℝ} (h : a * b * c = 1) (haux : 1 + a + a * b ≠ 0) :
    a / (a * b + a + 1) + b / (b * c + b + 1) + c / (c * a + c + 1) = 1 := by
  -- need ne_zero condition to perform division
  have : a * b * c ≠ 0 := by rw [h]; norm_num
  have ha : a ≠ 0 := left_ne_zero_of_mul <| left_ne_zero_of_mul this
  have hb : b ≠ 0 := right_ne_zero_of_mul <| left_ne_zero_of_mul this
  --  Multiply the second fraction by \(a\).
  conv => lhs; lhs; rhs; rw [← mul_div_mul_left _ _ ha]
  --  Multiply the third fraction by \(ab\).
  conv => lhs; rhs; rw [← mul_div_mul_left _ _ (mul_ne_zero ha hb)]
  -- Thus, we get:
  --  \[
  --  \frac{a}{ab + a + 1} + \frac{ab}{abc + ab + a} + \frac{abc}{abca + abc + ab}
  --  \]
  rw [show a * (b * c + b + 1) = a*b*c + a*b + a by ring]
  rw [show a*b*(c * a + c + 1) = a*b*c*a + a*b*c + a*b by ring]
  -- **Simplify the expression using \(abc = 1\):**
  rw [h, one_mul]
  ring_nf
  -- **Combine the terms with the same denominator:**
  rw [← add_mul]
  nth_rw 2 [← one_mul (1 + a + a * b)⁻¹]
  rw [← add_mul, show a * b + a + 1 = 1 + a + a * b by ring]
  exact mul_inv_cancel₀ haux
