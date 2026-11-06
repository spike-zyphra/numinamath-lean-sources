import Mathlib

/- Folklore

The function $f(x)$ is defined for all $x$, except 1, and satisfies the equation: $(x-1) f\left(\frac{x+1}{x-1}\right)=x+f(x)$. Find $f(-1)$. -/
theorem algebra_168105 {f : ℝ → ℝ} (hf : ∀ x, x ≠ 1 → (x - 1) * f ((x + 1) / (x - 1)) = x + f x) :
    f (-1) = -1 := by
  -- check x=0 and x=-1
  have h0:= hf 0 (by norm_num); simp at h0
  have hn1:= hf (-1) (by norm_num); simp at hn1; norm_num at hn1
  -- conclusion is obvious
  linarith