import Mathlib

/- Given that the point $(8,8)$ is on the graph of $y=\frac 14f\left(\frac 12x\right)$, there is one point that must be on the graph of $y=f(x)$. What is the sum of coordinates of that point? -/
theorem algebra_19359 {f : ℝ → ℝ} (h : f ≠ 0) (h' : 8 = 1 / 4 * f (1 / 2 * 8)) :
    32 = f 4 ∧ 32 + 4 = 36 := by
    -- split the goals
    constructor
    .   -- solve the first goal
        -- trivial transformation
        have h1 : (1 : ℝ) / 2 * 8 = 4 := by linarith
        rw [h1] at h'
        linarith
    .   linarith -- trivial calculation
