import Mathlib

/- Let $x$, $y$, and $z$ be real numbers such that $x+y+z=20$ and $x+2y+3z=16$. What is the value of $x+3y+5z$?

[i]Proposed by James Lin[/i] -/
theorem algebra_48023 (x y z : ℝ) (h₀ : x + y + z = 20) (h₁ : x + 2 * y + 3 * z = 16) :
    x + 3 * y + 5 * z = 12 := by 
  have ht := h₁.symm
  linarith