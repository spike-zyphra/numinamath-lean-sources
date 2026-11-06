import Mathlib

/- Rationalize the denominator: $\frac{1}{\sqrt{8}+\sqrt{50}+\sqrt{18}}$. -/
theorem algebra_22166 : 1 / (Real.sqrt 8 + Real.sqrt 50 + Real.sqrt 18) = Real.sqrt 2 / 20 := by
  -- $8 = 2 \cdot 2^2$
  have eq1 : (8 : ℝ) = 2 * 2 ^ 2 := by
    norm_num
  -- $50 = 2 \cdot 5^2$
  have eq2 : (50 : ℝ) = 2 * 5 ^ 2 := by
    norm_num
  -- $18 = 2\cdot 3^2$
  have eq3 : (18 : ℝ) = 2 * 3 ^ 2 := by
    norm_num
  -- $\sqrt{8}+\sqrt{50}+\sqrt{18}$ simplifies to $2\sqrt{2} + 5\sqrt{2} + 3\sqrt{2} = 10\sqrt{2}$
  have eq4 : Real.sqrt 8 + Real.sqrt 50 + Real.sqrt 18 = 10 * Real.sqrt 2 := by
    rw [eq1, eq2, eq3, Real.sqrt_mul, Real.sqrt_mul, Real.sqrt_mul, Real.sqrt_sq, Real.sqrt_sq, Real.sqrt_sq]
    ring
    all_goals norm_num
  rw [eq4]
  -- Simply multiply top and bottom by $\sqrt{2}$ to get $\frac{\sqrt{2}}{10\cdot2}= \boxed{\frac{\sqrt{2}}{20}}$
  field_simp
  rw [mul_comm, mul_assoc, ← pow_two, Real.sq_sqrt]
  norm_num
  exact zero_le_two
