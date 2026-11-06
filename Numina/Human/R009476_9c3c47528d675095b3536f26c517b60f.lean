import Mathlib

/-The first and thirteenth terms of an arithmetic sequence are $\frac79$ and $\frac45$, respectively. What is the seventh term?-/
theorem algebra_14263 {f : ℕ → ℝ} {d : ℝ} (hf: ∀n, f (n + 1) = f n + d) (hf₁: f 1 = 7/9) (hf₂: f 13 = 4/5) : f 7 = 71/90 := by
  -- Since the seventh term is halfway between the first term and thirteenth term, it is simply the average of these terms, or \[\frac{7/9 + 4/5}{2} = \boxed{\frac{71}{90}}.\]
  have hf₁₃ : f 13 = f 7 + 6 * d := by
    repeat rw [hf]
    linarith
  have hf₇ : f 7 = f 1 + 6 * d := by
    repeat rw [hf]
    linarith
  rw [hf₁] at hf₇
  rw [hf₂] at hf₁₃
  linarith
