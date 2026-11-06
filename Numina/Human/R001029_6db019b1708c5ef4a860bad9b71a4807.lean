import Mathlib

/- For some constants $a$ and $b,$ let \[f(x) = \left\{
\begin{array}{cl}
9 - 2x & \text{if } x \le 3, \\
ax + b & \text{if } x > 3.
\end{array}
\right.\]The function $f$ has the property that $f(f(x)) = x$ for all $x.$ What is $a + b?$ -/
theorem algebra_19972 {a b : ℝ} (f : ℝ → ℝ)
    (h₀ : ∀ x, x ≤ 3 → f x = 9 - 2 * x)
    (h₁ : ∀ x, x > 3 → f x = a * x + b)
    (h₂ : ∀ x, f (f x) = x) :
    a + b = 4 := by
    -- 计算 f(0)，因为 0 ≤ 3
    have h1 := h₀ 0 (by linarith)
    -- 计算 f(1)，因为 1 ≤ 3
    have h2 := h₀ 1 (by linarith)
    -- 应用 f(f(x)) = x 于 x = 0
    have h3 := h₂ 0
    -- 应用 f(f(x)) = x 于 x = 1
    have h4 := h₂ 1
    -- 在 h3 中代入 f(0) 的值
    rw [h1] at h3
    -- 在 h4 中代入 f(1) 的值
    rw [h2] at h4
    simp at h3 h4
    -- 计算 f(9)，因为 9 > 3
    replace h1 := h₁ 9 (by linarith)
    -- 计算 f(7)，因为 9-2 = 7 > 3
    replace h2 := h₁ (9 - 2) (by linarith)
    -- 在 h3 中代入 f(9) 的值
    rw [h1] at h3
    -- 在 h4 中代入 f(7) 的值
    rw [h2] at h4
    -- 使用线性算术求解
    linarith
