import Mathlib

/- 19. Let $f$ and $g$ be functions such that for all real numbers $x$ and $y$,

$$

g(f(x+y))=f(x)+(x+y) g(y) .

$$


Find the value of $g(0)+g(1)+\cdots+g(2013)$. -/
theorem algebra_102610 (f g : ℝ → ℝ) (h : ∀ x y, g (f (x + y)) = f x + (x + y) * g y) :
    ∑ i in Finset.range 2014, g i = 0 := by
  -- pluggin in x and -x we get g(f(0)) = f(x), this means f(x) is fixed value
  have h1 (x : ℝ) : g (f 0) = f x := by
    specialize h x (-x)
    ring_nf at h
    assumption
  -- in particular g(f(0)) = f(0)
  have h2 : g (f 0) = f 0 := h1 0
  -- now plug in (1-x) and x to isolate the g(x)
  have h3 (x : ℝ) : g (f 1) = f (1 - x) + g x := by
    specialize h (1 - x) x
    ring_nf at h
    assumption
  -- using the fact of f(x) = g(f(0)) = f(0) we get g(x) = 0
  have h4 (x : ℝ) : g x = 0 := by
    specialize h3 x
    rw [← h1, ← h1 (1 -x), h2, h2] at h3
    linarith
  -- so all the terms are 0, and sum is 0
  simp_rw [h4]
  simp