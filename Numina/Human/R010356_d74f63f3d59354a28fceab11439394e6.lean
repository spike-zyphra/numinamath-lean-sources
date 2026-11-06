import Mathlib

/- Suppose $a$, $b$, $c$ and $d$ are integers satisfying: $a-b+c=5$, $b-c+d=6$, $c-d+a=3$, and $d-a+b=2$. What is the value of $a+b+c+d$? -/
theorem algebra_10272 {a b c d : ℤ} (h₀ : a - b + c = 5) (h₁ : b - c + d = 6) (h₂ : c - d + a = 3) (h₃ : d - a + b = 2) :
    a + b + c + d = 16 := by 
  have h₄ : a + b + c + d = 16 := by linarith
  exact h₄