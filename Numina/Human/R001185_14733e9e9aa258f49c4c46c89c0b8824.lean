import Mathlib

/- If $c$ is a nonzero constant such that $x^2+cx+9c$ is equal to the square of a binomial, then what is $c$? -/
theorem algebra_20947 {c : ℝ} (hc : c ≠ 0) (h : ∃ a b, ∀ x, x^2 + c * x + 9 * c = (a + b * x)^2) :
    c = 36 := by
  -- if $x^2 + cx + 9c = (a+bx)^2$
  rcases h with ⟨a, b, h⟩
  have eq1 := h 0
  -- $a^2 = 9c$
  ring_nf at eq1
  -- $a \neq 0$
  have ane : a ≠ 0 := by
    by_contra contra
    rw [contra, zero_pow] at eq1
    simp only [mul_eq_zero, OfNat.ofNat_ne_zero, or_false] at eq1
    contradiction
    norm_num
  -- $c = 2ab$
  have ceq : c = 2 * a * b := by
    have mid := h 1
    ring_nf at mid
    have mid2 := h (-1)
    ring_nf at mid2
    linarith
  rw [ceq, pow_two, mul_comm 2, mul_assoc a, mul_assoc a] at eq1
  apply mul_eq_mul_left_iff.mp at eq1
  rcases eq1 with eq1 | eq1
  -- $a = 18 b$
  ring_nf at eq1
  apply eq_div_of_mul_eq (by norm_num) at eq1
  have eq2 := h 2
  rw [ceq, eq1] at eq2
  apply eq_sub_of_add_eq at eq2
  apply eq_sub_of_add_eq at eq2
  ring_nf at eq2
  -- $a = 18$, so $c = 36$
  field_simp at eq2
  have aeq : a ^ 2 = (18) ^ 2 := by
    rw [← eq2]
    norm_num
  apply eq_or_eq_neg_of_sq_eq_sq at aeq
  rcases aeq with aeq | aeq
  rw [ceq, eq1, aeq]
  norm_num
  rw [ceq, eq1, aeq]
  norm_num
  contradiction