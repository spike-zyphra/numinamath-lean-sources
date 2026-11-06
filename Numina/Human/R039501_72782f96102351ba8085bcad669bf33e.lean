import Mathlib

/- Prove that

$$
(1+a b c)\left(\frac{1}{a}+\frac{1}{b}+\frac{1}{c}\right) \geq 3+a+b+c
$$

for any real numbers $a, b, c \geq 1$. -/

theorem algebra_606235 (a b c : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    (1 + a * b * c) * (1 / a + 1 / b + 1 / c) ≥ 3 + a + b + c := by
  -- Simplify the inequality and clear denominator, then reduce to normal form.
  field_simp [add_mul]
  rw [le_div_iff₀ (show 0 < a * b * c by positivity)]
  ring_nf
  -- Now we prove that 2xy - (x + y) ≥ 0 for x, y ≥ 1.
  have aux_ineq (x y : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) : 2 * x * y - (x + y) ≥ 0 := by
    -- 2xy - (x + y) = x(y - 1) + y(x - 1) ≥ 0.
    calc
      2 * x * y - (x + y) = x * (y - 1) + y * (x - 1) := by ring
      _ ≥ 0 := by
        apply add_nonneg
        apply mul_nonneg (by positivity) (sub_nonneg_of_le hy)
        apply mul_nonneg (by positivity) (sub_nonneg_of_le hx)
  -- Apply the auxiliary inequality to prove an equivalent form of the inequality.
  have equiv_ineq : ((2 * a * b - (a + b)) * (a * b - 1)) / (2 * a * b) + ((2 * b * c - (b + c)) * (b * c - 1)) / (2 * b * c) + ((2 * c * a - (c + a)) * (c * a - 1)) / (2 * c * a) ≥ 0 := by
    -- Apply the auxiliary inequality to each term, and use the fact that a, b, c ≥ 1.
    apply add_nonneg
    apply add_nonneg
    apply div_nonneg
    apply mul_nonneg (aux_ineq a b ha hb)
    nlinarith only [ha, hb]
    positivity
    apply div_nonneg
    apply mul_nonneg (aux_ineq b c hb hc)
    nlinarith only [hb, hc]
    positivity
    apply div_nonneg
    apply mul_nonneg (aux_ineq c a hc ha)
    nlinarith only [hc, ha]
    positivity
  -- Now we multiply the inequality by 2abc.
  apply mul_nonneg (show 0 ≤ 2 * a * b * c by positivity) at equiv_ineq
  -- Simplify the expression by algebra manipulations.
  rw [mul_add, mul_add, <-mul_div_assoc, mul_assoc, mul_div_cancel_left₀, <-mul_div_assoc, mul_assoc (2 * a), mul_assoc 2 a (b * c), mul_comm a (b * c), <-mul_assoc 2 (b * c), <-mul_assoc 2 b, mul_assoc, mul_assoc, mul_div_cancel_left₀, <-mul_div_assoc, mul_assoc (2 * b), mul_assoc 2 b (c * a), mul_comm b (c * a), <-mul_assoc 2 (c * a), <-mul_assoc 2 c a, mul_assoc, mul_assoc, mul_div_cancel_left₀] at equiv_ineq
  ring_nf at equiv_ineq
  -- Use this equivalent form to prove the original inequality.
  linarith only [equiv_ineq]
  nlinarith only [hc, ha]
  nlinarith only [hb, hc]
  nlinarith only [ha, hb]
