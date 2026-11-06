import Mathlib

/- Given that $f(x)$ is an odd function, and when $x < 0$, $f(x) = x^3 + x^2$, then $f(2) = \boxed{4}$. -/
theorem algebra_8976 {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x) (hf : ∀ x < 0, f x = x ^ 3 + x ^ 2) :
    f 2 = 4 := by
  -- The function is odd, so f(-x) = -f(x)
  calc f 2 = -f (-2) := by linarith [hodd 2]
         _ = -((-2) ^ 3 + (-2) ^ 2) := by rw [hf (-2) (by norm_num)]
         _ = 4 := by norm_num
