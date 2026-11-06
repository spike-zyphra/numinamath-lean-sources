import Mathlib

/- The value of $x$ that makes the equation $x = -x$ true is 0. -/
theorem algebra_9296 {x : ℝ} (h : x = -x) : x = 0 := by
  -- Since $x = -x$, by rearranging the terms, we get $2x = 0$, therefore, $x = 0$
  let hx := congrArg (fun t => t + x) h; simp at hx
  exact hx
