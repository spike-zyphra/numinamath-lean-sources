import Mathlib

theorem algebra_251687 : {x : ℝ | x^2 - 5 * abs x + 6 = 0} = {-2, 2, -3, 3} := by
  ext x; simp
  constructor
  · -- If $x^{2}-5|x|+6=0$, then $x=-2,2,-3,3$
    intro hx
    by_cases h : 0 ≤ x
    · -- When $x \geq 0$, $|x| = x$, so $x^{2}-5x+6=0$
      rw [abs_of_nonneg h] at hx
      have : (x - 2) * (x - 3) = 0 := by linarith
      cases' (mul_eq_zero.mp this) with hx1 hx2
      · -- $x = 2$ is a solution
        right
        left
        linarith
      · -- $x = 3$ is a solution
        right
        right
        right
        linarith
    · -- When $x < 0$, $|x| = -x$, so $x^{2}+5x+6=0$
      push_neg at h
      rw [abs_of_neg h] at hx
      have : (x + 2) * (x + 3) = 0 := by linarith
      cases' (mul_eq_zero.mp this) with hx1 hx2
      · -- $x = -2$ is a solution
        left
        linarith
      · -- $x = -3$ is a solution
        right
        right
        left
        linarith
  · -- If $x=-2,2,-3,3$, then $x^{2}-5|x|+6=0$.
    rintro (rfl | rfl | rfl | rfl)
    · norm_num
    · norm_num
    · norm_num
    · norm_num
