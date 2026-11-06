import Mathlib

/-The solution to the equation $x + 2a - 6 = 0$ is $x = -2$. Find the value of $a$.-/
theorem algebra_9191 (a : ℝ) : (-2 + 2 * a - 6 = 0) ↔ a = 4 := by
  -- divide the problem into solving for $a$ and checking it is solution
  constructor
  -- to solve for $a$, we first get the given equation out.
  intro h
  -- cancel out $-6$ and $-2$ on the LHS.
  have : - 2 + 2 * a - 6 + 6 = 0 + 6 := by rw [h]
  simp only [sub_add_cancel, zero_add] at this
  have : 2 + (- 2 + 2 * a) = 2 + 6 := by rw [this]
  simp only [add_neg_cancel_left] at this
  -- separate $a$ and we get the desired result.
  have : 2 * a * (1 / 2) = (2 + 6) * (1 / 2) := by rw [this]
  rw [mul_comm] at this; simp only [one_div, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, IsUnit.inv_mul_cancel_left] at this
  rw [this]; norm_num
  -- the other side only needs a quick check.
  intro h; rw[h]; norm_num