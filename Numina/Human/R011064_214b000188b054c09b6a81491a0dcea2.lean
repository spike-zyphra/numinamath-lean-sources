import Mathlib

/- Given that \\(f(x)\\) is an odd function defined on \\(\mathbb{R}\\), and when \\(x \in (-\infty, 0)\\), \\(f(x) = -x^{2} + 2x\\), find the value of \\(f(3)\\). -/
theorem algebra_9213 {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x) (hf : ∀ x < 0, f x = -x^2 + 2 * x) :
    f 3 = 15 := by
  -- f(3) = -f(-3) = -(-(-3)^2 + 2 * (-3)) = 15
  calc f 3 = -f (-3) := by linarith [hodd 3]
         _ = -(-(-3)^2 + 2 * (-3)) := by rw [hf (-3) (by norm_num)]
         _ = 15 := by norm_num
