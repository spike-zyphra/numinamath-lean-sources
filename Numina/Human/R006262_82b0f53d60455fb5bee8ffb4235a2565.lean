import Mathlib

/- Let $k$ be a positive integer. Consider the ring $\mathbb{Z}[\sqrt{-k}]$, whose elements are numbers of the form $a_1 + a_2\sqrt{-k}$ where $a_1, a_2$ are integers and $\sqrt{-k}$ is a symbol whose square is $-k$. The sum and product are defined in the usual way. For an element $\alpha = a_1 + a_2\sqrt{-k}$ in this ring, define its norm as $N(\alpha) = a_1^2 + k a_2^2$.
Let $\alpha = x_1 + y_1\sqrt{-k}$ and $\beta = x_2 + y_2\sqrt{-k}$ be two elements in $\mathbb{Z}[\sqrt{-k}]$. Show that $N(\alpha\beta) = N(\alpha)N(\beta)$. -/
theorem number_theory_635260 (k : ℤ) (h : 0 < k) (α β : ℤ√(-k)) : (α * β).norm = α.norm * β.norm := by
  -- We expand the definitions.
  simp only [Zsqrtd.norm, Zsqrtd.mul_im, Zsqrtd.mul_re]
  -- Ring identity.
  ring