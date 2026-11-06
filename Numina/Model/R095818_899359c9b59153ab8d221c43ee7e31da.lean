import Mathlib

/- Define $\left[a,b\right]$ as the characteristic number of the linear function $y=ax+b$. If the linear function with the characteristic number $\left[k,k^{2}-1\right]$ is a direct proportion function, then the value of $k$ is ___          ___. -/
theorem algebra_8177 {k : ℝ} (hk : k ≠ 0) (h : ∀ x, k * x + (k ^ 2 - 1) = k * x) :
    k = 1 ∨ k = -1 := by
  -- Substitute x = 0 in the equation.
  have h1 := h 0
  -- Simplify to get k^2 - 1 = 0.
  have hk2 : k ^ 2 - 1 = 0 := by
    linarith
  -- Rearrange to get k^2 = 1.
  have hk2_1 : k ^ 2 = 1 := by
    linarith
  -- Now that we have k^2 = 1, we can take the square root.
  have h2 : k = 1 ∨ k = -1 := by
    rw [sq_eq_one_iff] at hk2_1
    exact hk2_1
  exact h2