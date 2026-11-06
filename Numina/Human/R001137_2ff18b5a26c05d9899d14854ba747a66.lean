import Mathlib

/-
Let $f(x) = 2x - 3$ and $g(f(x)) = 5-4x.$ Find $g(4).$-/

theorem algebra_20684 {f g : ℝ → ℝ} (hf : f = fun x => 2 * x - 3) (hg : ∀ x, g (f x) = 5 - 4 * x) :

    g 4 = -9 := by
    --We don't know $g(x),$ so we don't have an expression we can simply stick $4$ in to get an answer. We do, however, know that $g(f(x)) = 5-4x.$ So, if we can figure out what to put into $f(x)$ such that $4$ is output, we can use our expression for $g(f(x))$ to find $g(4).$
    have heq : f (7/2) = 4 := by
      rw[hf]
      simp; ring_nf
    --Since $f(x) = 2x-3,$ the value of $x$ such that $f(x) = 4$ is the solution to the equation $2x-3 = 4,$ which is $x = 7/2.$ So, we have $f(7/2) = 4.$ Therefore, if we let $x=7/2$ in $g(f(x)) = 5-4x,$ we have \[g(f(7/2)) = 5-4\cdot\frac{7}{2} \implies g(4) = 5-14 = \boxed{-9}.\]
    have heq2 := hg (7/2)
    rw[heq] at heq2
    ring_nf at heq2
    exact heq2
