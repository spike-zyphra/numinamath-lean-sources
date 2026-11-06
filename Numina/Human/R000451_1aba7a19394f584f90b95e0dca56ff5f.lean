import Mathlib

/- For some constants $a$ and $b,$ let \[f(x) = \left\{
\begin{array}{cl}
ax + b & \text{if } x < 2, \\
8 - 3x & \text{if } x \ge 2.
\end{array}
\right.\]The function $f$ has the property that $f(f(x)) = x$ for all $x.$ What is $a + b?$ -/
theorem algebra_10681 {a b : ℝ} (f : ℝ → ℝ)
    (h₀ : ∀ x, x < 2 → f x = a * x + b)
    (h₁ : ∀ x, x ≥ 2 → f x = 8 - 3 * x)
    (h₂ : ∀ x, f (f x) = x) :
    a + b = 7 / 3 := by
  -- set x=3, we have f(3) = 8-3x3 = -1, and f(f(3)) = 3 = f(-1)
  have h1: f (-1) = 3 := by
    have ht1: f 3 = -1 := by
      rw [h₁ 3 (by norm_num)]; ring
    have ht2: f (f 3) = 3 := h₂ 3
    rw [← ht1, ht2]
  -- similarly, set x=4, we have f(4) = 8-3x4 = -4, and f(f(4)) = 4 = f(-4)
  have h2: f (-4) = 4 := by
    have ht1: f 4 = -4 := by
      rw [h₁ 4 (by norm_num)]; ring
    have ht2: f (f 4) = 4 := h₂ 4
    rw [← ht1, ht2]
  -- f(-1) = -a+b, f(-4) = -4a +b, we get two equations of a and b.
  rw [h₀ (-1) (by norm_num)] at h1
  rw [h₀ (-4) (by norm_num)] at h2
  -- -a+b=3, -4a+b=4. we can solve a and b
  have aeq: a = -1/3 := by
    have ht1: (1:ℝ) = 4-3 := by norm_num
    rw [ht1, ← h2]
    nth_rw 1 [← h1]
    ring
  have beq: b = 8/3 := by
    rw [aeq] at h1; simp at h1
    have ht1: (8/3:ℝ) = 3 - 1/3 := by norm_num
    rw [ht1]
    nth_rw 1 [← h1]; ring
  -- so a+b = -1/3 + 8/3 = 7/3
  rw [aeq, beq]; ring