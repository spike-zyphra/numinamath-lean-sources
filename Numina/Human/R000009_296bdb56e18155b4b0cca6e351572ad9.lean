import Mathlib

/- Vasya thought of two numbers. Their sum equals their product and equals their quotient. What numbers did Vasya think of?-/
theorem algebra_4021 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) (h1 : x + y = x * y) (h2 : x * y = x / y) :
    x = 1 / 2 ∧ y = -1 := by
--   Multiplying both sides by \(y\):
-- \[
-- xy \cdot y = x
-- \]
  rw [← mul_left_inj' hy, div_mul_cancel₀ x hy] at h2
--    we can divide both sides by \(x\):
-- \[
-- y^2 = 1
-- \]
  nth_rw 2 [← mul_one x] at h2
  rw [mul_assoc, mul_right_inj' hx] at h2
--   Thus,
-- \[
-- y = \pm 1
-- \]
  rw [← sq, show (1 : ℝ) = 1 ^ 2 by norm_num, sq_eq_sq_iff_eq_or_eq_neg] at h2
  rcases h2 with h2 | h2
--    **When \(y = 1\)**:
-- \[
-- x + y = xy
-- \]
-- \[
-- x + 1 = x \cdot 1
-- \]
-- \[
-- x + 1 = x
-- \]
-- This leads to a contradiction since \(1 \neq 0\). Therefore, \(y = 1\) is not a valid solution.
  . rw [h2, mul_one] at h1
    linarith
--   **When \(y = -1\)**:
-- \[
-- x + y = xy
-- \]
-- \[
-- x - 1 = x \cdot (-1)
-- \]
-- \[
-- x - 1 = -x
-- \]
-- Adding \(x\) to both sides:
-- \[
-- 2x - 1 = 0
-- \]
-- Solving for \(x\):
-- \[
-- 2x = 1
-- \]
-- \[
-- x = \frac{1}{2}
-- \]
  rw [h2] at h1
  replace h1 := sub_eq_zero_of_eq h1
  ring_nf at h1
  rw [add_comm, add_eq_zero_iff_eq_neg, neg_neg] at h1
  replace h1 := eq_div_of_mul_eq (by norm_num) h1
  exact ⟨h1, h2⟩
