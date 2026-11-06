import Mathlib

/- 4A. Given are $a_{1}, b_{1}, c_{1}, a_{2}, b_{2}, c_{2}$ positive real numbers. For them, it holds that $b_{1}^{2} \leq 4 a_{1} c_{1}$ and $b_{2}^{2} \leq 4 a_{2} c_{2}$. Prove that


$$

4\left(a_{1}+a_{2}+7\right)\left(c_{1}+c_{2}+2\right)>\left(b_{1}+b_{2}+1\right)^{2}

$$
 -/
theorem inequalities_254716 (a1 a2 b1 b2 c1 c2 : ℝ)
    (ha1 : 0 < a1) (ha2 : 0 < a2) (hb1 : 0 < b1) (hb2 : 0 < b2)
    (hc1 : 0 < c1) (hc2 : 0 < c2)
    (h1 : b1^2 ≤ 4 * a1 * c1) (h2 : b2^2 ≤ 4 * a2 * c2) :
    4 * (a1 + a2 + 7) * (c1 + c2 + 2) > (b1 + b2 + 1)^2 := by
  -- first we prove a lemma that if leading coefficient is 0 and b^2 ≤ 4*a*c then all values of quadratic expression are nonnegative
  have aux (a b c : ℝ) (ha : 0 < a) (h : b^2 ≤ 4 * a * c) (x : ℝ) : 0 ≤ a * x^2 + b * x + c := by
    convert_to 0 ≤ a * (x + b / (2 * a))^2 + (4 * a * c - b^2) / (4 * a)
    . ring_nf
      field_simp
      ring
    apply add_nonneg
    . apply mul_nonneg
      . exact le_of_lt ha
      . positivity
    . apply div_nonneg <;> linarith
  -- we use the lemma on a1,b1,c1 and a2,b2,c2
  have hx1 (x : ℝ) : 0 ≤ a1 * x^2 + b1 * x + c1 := aux a1 b1 c1 ha1 h1 x
  have hx2 (x : ℝ) : 0 ≤ a2 * x^2 + b2 * x + c2 := aux a2 b2 c2 ha2 h2 x
  -- we also prove 0 < 7*x^2 + 1 * x + 2 by completing the square
  have hx3 (x : ℝ) : 0 < 7 * x^2 + 1 * x + 2 := by
    suffices 0 < (x + 1/14)^2 + (2/7 - (1/14)^2) by linarith
    apply add_pos_of_nonneg_of_pos
    . positivity
    . norm_num
  -- we add up the 3 inequalities
  have hx4 (x : ℝ) : 0 < (a1 + a2 + 7) * (x * x) + (b1 + b2 + 1) * x + (c1 + c2 + 2) := by
    linear_combination (hx1 x) + (hx2 x) + (hx3 x)
  -- now the exprssion being positive always implies discriminant is negative, which implies target
  have := discrim_lt_zero (by linarith) hx4
  simp [discrim] at this
  linarith