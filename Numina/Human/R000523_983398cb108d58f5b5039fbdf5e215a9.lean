import Mathlib

/-Let $f(x) = Ax + B$ and $g(x) = Bx + A$, where $A \neq B$. If $f(g(x)) - g(f(x)) = B - A$, what is $A + B$?

The final answer is $ \boxed{0} $-/
theorem algebra_11836 {A B : ℝ} (hA : A ≠ B) (f g : ℝ → ℝ)
  (hf : f = fun x => A * x + B) (hg : g = fun x => B * x + A)
  (hfg : ∀ x, f (g x) - g (f x) = B - A) : A + B = 0 := by
    -- First we find that $f(g(x)) = A(Bx + A) + B = ABx + A^2 + B$ and
    -- $g(f(x)) = B(Ax + B) + A = ABx + B^2 + A$.
    simp [hf, hg] at hfg
    specialize hfg 1
    -- Now we plug back in. \begin{align*}
    -- f(g(x)) - g(f(x)) &= B - A \\
    -- (ABx + A^2 + B) - (ABx + B^2 + A) &= B - A \\
    -- A^2 - B^2 + B - A &= B - A \\
    -- A^2 - B^2 &= 0 \\
    -- (A-B)(A+B) &= 0
    -- \end{align*}
    have : (A - B) * (A + B) = 0 := by nlinarith
    -- Since we are given that $A \neq B$, this means that $A + B = \boxed{0}.$
    rw [mul_eq_zero] at this
    refine (or_iff_right ?_).1 this
    intro AB
    have AeqB : A = B := by linarith
    tauto
