import Mathlib

/-The solution to the linear equation $\frac{2}{3}x-2=4$ is ____.-/
theorem algebra_9155 (x : ℝ) : (2 / 3 * x - 2 = 4) ↔ (x = 9) := by
  constructor
  intro h
  -- cancel to get a monomial of $x$
  have h : 2 / 3 * x - 2 + 2 = 6 := by rw [h]; norm_num
  simp only [sub_add_cancel] at h
  have : 2 / 3 * x = x * 2 / 3 := by ring
  rw [this] at h
  -- separate $x$ and get the desired result
  have h : x * 2 / 3 * 3 = 18 := by rw [h]; norm_num
  simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    IsUnit.div_mul_cancel] at h
  have : x * 2 / 2 = 9 := by rw [h]; norm_num
  simp only [isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    IsUnit.mul_div_cancel_right] at this
  exact this
  -- the other side requires only a quick check
  intro h; rw [h]; norm_num