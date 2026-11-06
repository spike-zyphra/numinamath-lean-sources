import Mathlib

/- Let

$$
A=\frac{1}{6}\left(\left(\log _{2}(3)\right)^{3}-\left(\log _{2}(6)\right)^{3}-\left(\log _{2}(12)\right)^{3}+\left(\log _{2}(24)\right)^{3}\right)
$$

Compute $2^{A}$. -/
theorem algebra_609213 (A : ℝ) (hA : A = 1 / 6 * ((Real.logb 2 3) ^ 3 - (Real.logb 2 6) ^ 3 - (Real.logb 2 12) ^ 3 + (Real.logb 2 24) ^ 3)) : (2 : ℝ) ^ A = 72 := by
  -- Let a = Real.logb 2 3.
  let a := Real.logb 2 3
  rw [show Real.logb 2 3 = a by rfl, show Real.logb 2 6 = a + 1 by rw [show (6 : ℝ) = 3 * 2 by norm_num, Real.logb_mul]; all_goals simp, show Real.logb 2 12 = a + 2 by rw [show (12 : ℝ) = 3 * 2 ^ 2 by norm_num, Real.logb_mul, Real.logb_pow]; all_goals simp, show Real.logb 2 24 = a + 3 by rw [show (24 : ℝ) = 3 * 2 ^ 3 by norm_num, Real.logb_mul, Real.logb_pow]; all_goals simp] at hA
  -- It simplifies to A = 2a + 3.
  replace hA : A = 2 * a + 3 := by linarith
  rw [hA, Real.rpow_add, mul_comm 2, Real.rpow_mul, Real.rpow_logb]
  all_goals
    norm_num
