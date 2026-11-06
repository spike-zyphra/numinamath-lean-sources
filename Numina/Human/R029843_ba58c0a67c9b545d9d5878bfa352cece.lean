import Mathlib

/- A line $l$ is the graph of $y = ax + b$. Line $l_1$ is $l$ shifted 3 units to the left and two units downward and passes through the points $(5,8)$ and $(7,14)$. What is $a - b$? -/
theorem algebra_22475 {a b : ℝ} (l₁ : ℝ → ℝ) (h : ∀ x, l₁ x = a * (x + 3) + b - 2)
    (ha' : l₁ 5 = 8) (hb' : l₁ 7 = 14) : a - b = 17 := by
  rw [h] at ha' hb'
  linarith