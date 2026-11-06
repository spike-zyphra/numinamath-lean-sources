import Mathlib

/-Let $f(x)$ be an even function, and for $x \geq 0$, $f(x) = 2x - x^2$ ($a,b \in \mathbb{R}$). Find $f(x)$ for $x < 0$.-/
theorem algebra_9179 {f : ℝ → ℝ} (h₀ : ∀ x, f (-x) = f x)
    (h₁ : ∀ x ≥ 0, f x = 2 * x - x ^ 2) :
    ∀ x < 0, f x = -2 * x - x ^ 2 := by 
    intro x h
    -- because $x<0$, $-x≥0$ so we can plug in $-x$ into the given function and calculate the result.
    have : - x ≥ 0 := by linarith
    specialize h₁ (-x); have : f (-x) = 2 * (-x) - (-x) ^ 2 := h₁ this
    -- using the property of even functions we change $-x$ in the final expression to $x$ to get the desired result.
    specialize h₀ x; rw [← h₀, this]; ring