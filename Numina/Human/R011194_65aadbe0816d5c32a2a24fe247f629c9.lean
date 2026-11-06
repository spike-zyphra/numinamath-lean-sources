import Mathlib

open Real

/- 11.11. Prove that


$$

4 \operatorname{arctg} \frac{1}{5}-\operatorname{arctg} \frac{1}{239}=\frac{\pi}{4}

$$
 -/
theorem algebra_225501 : 4 * Real.arctan (1 / 5) - Real.arctan (1 / 239) = Real.pi / 4 := by
  -- Use 2 * arctan formula twice, arctan addition formula, and calculate
  rw [show (4 : ℝ) * _ = 2 * (2 * _) by ring, two_mul_arctan, two_mul_arctan, sub_eq_iff_eq_add, ← arctan_one, arctan_add (by norm_num)] <;> norm_num