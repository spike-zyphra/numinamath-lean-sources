import Mathlib

/-Given that $f(x) = \begin{cases} 2^{x} - 3, & x > 0, \\ g(x), & x < 0 \end{cases}$ is an odd function, find $f(g(-2))$.-/
theorem algebra_9279 {f g : ℝ → ℝ} (hf : ∀ x, x > 0 → f x = 2 ^ x - 3)
(hg : ∀ x, x < 0 → f x = g x) (hodd : ∀ x, f x = - f (-x)) :
f (g (-2)) = 1 := by
-- Rewrite assumptions and find out an explicit expression for $g$
  have h'g : ∀ x, x < 0 → g x = - 2 ^ (-x) + 3 := by
    intro x hx
    have r1 := hg x hx
    have r2 := hodd x
    have r3 := hf (-x) (show (0:ℝ)<(-x) by linarith)
    linarith
-- Plug in $x=-2$ and compute $g(-2)$
  have gneg2 := h'g (-2) (show -(2:ℝ)<0 by simp)
  ring_nf at gneg2
-- Plug in $g(-2)=-1$ to the final goal and prove it
  rw [gneg2, hg, h'g]; ring
  norm_num; norm_num