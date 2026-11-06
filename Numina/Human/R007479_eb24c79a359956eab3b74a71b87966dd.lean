import Mathlib

/-Given a linear function $y=mx+m-2$ is a direct proportion function,
then $m=\_\_\_\_\_\_$.-/
theorem algebra_9434 {m : ℝ} (h : ∃ c, ∀ x, m * x + m - 2 = c * x) :
    m = 2 := by
  rcases h with ⟨c, hc⟩
  have : m - 2 = 0 := by
    have := hc 0
    linarith
  -- For the function to be a direct proportion, we set this equal to $0$:
  -- \[m-2 = 0\]
  linarith
  -- Solving for $m$ gives us: \[m = 2\]