import Mathlib

/- Given $f(x)$ is an even function on $\mathbb{R}$ and satisfies $f(x+4) = f(x)$. For $x \in (0,2)$, $f(x) = 2x^2$. Find the value of $f(7)$. -/
theorem algebra_9156 {f : ℝ → ℝ} (h₀ : ∀ x, f (-x) = f x) (h₁ : ∀ x, f (x + 4) = f x) (h₂ : ∀ x ∈ Set.Ioo 0 2, f x = 2 * x ^ 2) : f 7 = 2 := by
  -- since f(x+4) = f(x), we continuously subtract 4, until the argument falls in an interval where the function is explicitly defined.
  have h1: f 3 = f 7 := by
    rcases h₁ 3 with ht1
    rw [← ht1]
    congr
    norm_num
  have h2: f 3 = f (-1) := by
    rcases h₁ (-1) with ht1
    rw [← ht1]
    congr
    norm_num
  -- notice that f(x) is an even function, so f(-1) = f(1).
  have h3: f (-1) = f 1 := h₀ 1
  rw [← h1, h2, h3]
  -- f(1) is explicitly defined. and we substitute back, f(7) is determined.
  have h4: f 1 = 2 := by
    have ht1: 1 ∈ Set.Ioo (0:ℝ) 2 := by norm_num
    rcases h₂ 1 with ht2
    have ht3: f 1 = 2 * 1^2 := ht2 ht1
    rw [ht3]
    norm_num
  exact h4