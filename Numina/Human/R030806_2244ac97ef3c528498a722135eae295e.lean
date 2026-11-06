import Mathlib
/-
Let $a,$ $b,$ $c,$ $d$ be real numbers such that

\begin{align*}

a + b + c + d &= 1, \\

a + 2b + 4c + 8d &= 16, \\

a - 5b + 25c - 125d &= 625, \\

a + 6b + 36c + 216d &= 1296.

\end{align*}Enter the ordered quadruple $(a,b,c,d).$-/
theorem algebra_21234 {a b c d : ℝ}
    (h₀ : a + b + c + d = 1)
    (h₁ : a + 2 * b + 4 * c + 8 * d = 16)
    (h₂ : a - 5 * b + 25 * c - 125 * d = 625)
    (h₃ : a + 6 * b + 36 * c + 216 * d = 1296) :
    a = 60 ∧ b = -88 ∧ c = 25 ∧ d = 4 := by
    --Consider the polynomial
    --\[p(x) = x^4 - dx^3 - cx^2 - bx - a.\]Then $p(1) = 1 - d - c - b - a = 0.$  Similarly,
    --\begin{align*}
    --p(2) &= 16 - 8d - 4c - 2b - a = 0, \\
    --p(-5) &= 625 - 125d - 25c - 5b - a = 0, \\
    --p(6) &= 1296 - 216d - 36c - 6b - a = 0.
    --\end{align*}Since $p(x)$ has degree 4 and is monic,
    --\begin{align*}
    --p(x) &= (x - 1)(x - 2)(x + 5)(x - 6) \\
    --&= x^4 - 4x^3 - 25x^2 + 88x - 60.
    --\end{align*}Hence, $(a,b,c,d) = \boxed{(60,-88,25,4)}.$
  --Gradually eliminate variables through Gaussian elimination method, and finally obtain a unique solution for each variable
  have ha : a = 60 := by
    --Eliminate other variables through a linear combination of equations, and finally obtain the value of a
    linarith [h₀, h₁, h₂, h₃]
  have hb : b = -88 := by
    --Eliminate other variables through a linear combination of equations, and finally obtain the value of b
    linarith [h₀, h₁, h₂, h₃]
  have hc : c = 25 := by
    --Eliminate other variables through a linear combination of equations, and finally obtain the value of c
    linarith [h₀, h₁, h₂, h₃]
  have hd : d = 4 := by
    --Eliminate other variables through a linear combination of equations, and finally obtain the value of d
    linarith [h₀, h₁, h₂, h₃]
  exact ⟨by assumption, by assumption, by assumption, by assumption⟩
