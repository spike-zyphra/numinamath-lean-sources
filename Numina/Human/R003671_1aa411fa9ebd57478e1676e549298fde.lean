import Mathlib

/- Let $a, b, c$ be real numbers such that if $|x| \leq 1$, then $\left|a x^{2}+b x+c\right| \leq 1$. Show that if $|x| \leq 1$, then $\left|c x^{2}+b x+a\right| \leq 2$ also holds. -/
theorem algebra_205783 (a b c : ℝ) (h : ∀ x : ℝ, |x| ≤ 1 → |a * x ^ 2 + b * x + c| ≤ 1) :
    ∀ x : ℝ, |x| ≤ 1 → |c * x ^ 2 + b * x + a| ≤ 2 := by
  rintro x hx
  -- write f and g as functions for the expressions
  let f (x : ℝ) := a * x^2 + b * x + c
  let g (x : ℝ) := c * x^2 + b * x + a
  -- we can write g(x) in terms of x and f(0), f(1), f(-1)
  have hg : 2 * g x = (1 + x) * f 1 + (1 - x) * f (-1) + 2 * f 0  * (x^2 - 1) := by
    simp [f, g]
    ring
  -- we will prove |2 * g x| ≤ 4, which implies our goal
  suffices |2 * g x| ≤ 4 by
    simp [g] at this
    rw [abs_mul] at this
    simp at this
    linarith
  calc
    -- first write g using f
    _ = |(1 + x) * f 1 + (1 - x) * f (-1) + 2 * f 0  * (x^2 - 1)| := by rw [hg]
    -- using triangle inequality we get following
    _ ≤ |1 + x| * |f 1| + |1 - x| * |f (-1)| + 2 * |f 0|  * |x^2 - 1| := by
      nth_rw 2 [show 2 = |(2 : ℝ)| by norm_num]
      rw [← abs_mul, ← abs_mul, ← abs_mul, ← abs_mul]
      trans |(1 + x) * f 1 + (1 - x) * f (-1)| + |2 * f 0  * (x^2 - 1)|
      . apply abs_add_le
      . gcongr
        apply abs_add_le
    -- now due to hypothesis about f, we get these bounds
    _ ≤ |1 + x| * 1 + |1 - x| * 1 + 2 * 1  * |x^2 - 1| := by
      gcongr <;> (apply h; norm_num)
    -- due to bounds on x, we can simplify absoulte values
    _ = 1 + x + 1 - x + 2 * (1 - x ^ 2) := by
      have hx' := abs_le.mp hx
      rw [abs_eq_self.mpr (by linarith), abs_eq_self.mpr (by linarith), abs_eq_neg_self.mpr]
      ring
      . suffices x^2 ≤ 1 by linarith
        simpa
    -- then goal is implied by nonegativity of x^2
    _ ≤ 4 := by
      suffices 0 ≤ x^2 by linarith
      positivity