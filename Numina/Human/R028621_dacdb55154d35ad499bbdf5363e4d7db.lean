import Mathlib


/-Let $\lfloor x \rfloor$ denote the greatest integer less than or equal to $x$. Then, the solution set of the inequality $\lfloor x \rfloor^2 - 5\lfloor x \rfloor - 36 \leq 0$ is.-/
theorem algebra_9303 (x : ℝ) :
⌊x⌋ ^ 2 - 5 * ⌊x⌋ - 36 ≤ 0 ↔ -4 ≤ x ∧ x < 10 := by
-- Factorize the LHS of the inequality
  rw [show ⌊x⌋ ^ 2 - 5 * ⌊x⌋ - 36 = (⌊x⌋ - 9) * (⌊x⌋ + 4) by ring]
-- Apply mul_nonpos_iff to split it to two inequalities and simplify them
  rw [mul_nonpos_iff]; simp; rw [← le_neg_iff_add_nonpos_right]
  rw [← neg_le_iff_add_nonneg]
-- Apply the properties of floor function and solve for bounds of $x$
  rw [show -(4:ℤ)=-3-1 by simp, show (9:ℤ)=10-1 by simp]
  rw [Int.floor_le_sub_one_iff, Int.floor_le_sub_one_iff]
  rw [Int.le_floor, Int.le_floor]; norm_cast; simp
-- Break "iff" and prove the final goals
  constructor; intro h; cases h; linarith
  constructor; linarith; linarith
  intro h; right; constructor; linarith; linarith