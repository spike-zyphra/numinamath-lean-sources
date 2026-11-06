import Mathlib

/- For the equation $x^{2}-kx-6=0$ with one root $x=-3$, the value of $k$ is ______. -/
theorem algebra_9445 {k : ℝ} (h : (-3)^2 - k * (-3) - 6 = 0) : k = -1 := by
  -- substitute x=-3 back into the equation (which is h), following are some calculations.
  have h1: (-3)^2 - k * (-3) - 6 = 3 * (k+1) := by ring
  rw [h1] at h
  have h2: (3:ℝ) ≠ 0 := by norm_num
  have h3: k+1 = 0 := by
    exact eq_zero_of_ne_zero_of_mul_left_eq_zero h2 h
  exact Eq.symm (neg_eq_of_add_eq_zero_left h3)