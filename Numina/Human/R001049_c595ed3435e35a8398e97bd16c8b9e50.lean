import Mathlib

/- When the graph of a certain function $f(x)$ is shifted $2$ units to the right and stretched vertically by a factor of $2$ (meaning that all $y$-coordinates are doubled), the resulting figure is identical to the original graph.

Given that $f(0)=0.1$, what is $f(10)$? -/
theorem algebra_20157 {f : ℝ → ℝ} (h : ∀ x, f (x + 2) = 2 * f x) (h0 : f 0 = 0.1) : f 10 = 3.2 := by
  -- Use the given equation to calculate f 10
  -- f 10 = 2 * f 8 = 4 * f 6 = 8 * f 4 = 16 * f 2 = 32 * f 0 = 3.2
  calc f 10
       _ = f (8 + 2) := by norm_num
       _ = 2 * f 8 := by rw [h]
       _ = 2 * (f (6 + 2)) := by norm_num
       _ = 2 * (2 * f 6) := by rw [h]
       _ = 2 * (2 * (f (4 + 2))) := by norm_num
       _ = 2 * (2 * (2 * f 4)) := by rw [h]
       _ = 2 * (2 * (2 * (f (2 + 2)))) := by norm_num
       _ = 2 * (2 * (2 * (2 * f 2))) := by rw [h]
       _ = 2 * (2 * (2 * (2 * (f (0 + 2))))):= by norm_num
       _ = 2 * (2 * (2 * (2 * (2 * f 0)))) := by rw [h]
       _ = 2 * (2 * (2 * (2 * (2 * 0.1)))) := by rw [h0]
       _ = 3.2 := by norm_num
