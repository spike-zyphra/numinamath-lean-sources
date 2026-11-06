import Mathlib

/- Given that the function $f(x)$ is an odd function, and when $x > 0$, $f(x)=x^{2}-2x+3$, determine the analytical expression of $f(x)$. -/
theorem algebra_9334 {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x) (hfpos : ∀ x > 0, f x = x ^ 2 - 2 * x + 3) :
    ∀ x, f x = if x < 0 then -x ^ 2 - 2 * x - 3 else (if x = 0 then 0 else x ^ 2 - 2 * x + 3) := by

  intro x

  -- Use trichotomy to split into three cases
  obtain h | h | h := lt_trichotomy x 0

  . -- Case x < 0
    simp [h]
    -- f x = -f (-x) = -((-x) ^ 2 - 2 * (-x) + 3)
    specialize hfpos (-x) (by linarith)
    linarith [hodd x]

  . -- Case x = 0
    simp [h]
    -- Odd functions map 0 to 0
    specialize hodd 0
    simp at hodd
    linarith

  . -- Case x > 0
    simp [(by linarith : ¬ x < 0), (by linarith : x ≠ 0)]
    exact hfpos x h
