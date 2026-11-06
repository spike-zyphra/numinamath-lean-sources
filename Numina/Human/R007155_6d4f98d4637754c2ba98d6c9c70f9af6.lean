import Mathlib

/- Let $f(x) = ax+b$, where $a$ and $b$ are real constants, and $g(x) = 2x - 5$. Suppose that for all $x$, it is true that $g(f(x)) = 3x + 4$. What is $a+b$? -/
theorem algebra_14975 {a b : ℝ} (f g : ℝ → ℝ) (hf : ∀ x, f x = a * x + b)
    (hg : ∀ x, g x = 2 * x - 5) (hfg : ∀ x, g (f x) = 3 * x + 4) :
    a + b = 6 := by 
  specialize hfg 1
  rw [hf, hg] at hfg
  linarith