import Mathlib

/- Suppose a function $f(x)$ has domain $(-\infty,\infty)$ and range $[-11,3]$. If we define a new function $g(x)$ by $$g(x) = f(6x)+1,$$ then what is the range of $g(x)$? Express your answer in interval notation. -/
theorem algebra_21855 (f : ℝ → ℝ) (hf : Set.range f = Set.Icc (-11) 3)
    (g : ℝ → ℝ) (hg : ∀ x, g x = f (6 * x) + 1) :
    Set.range g = Set.Icc (-10) 4 := by
    ext y
    constructor
    · -- $g(x) \in [-10, 4]$ for all $x$
      intro yin
      rcases yin with ⟨x, hx⟩
      rw [hg] at hx
      have fin : f (6 * x) ∈ Set.Icc (-11) 3 := by
        rw [← hf]
        exact Set.mem_range_self (6 * x)
      constructor
      rw [← hx]
      -- $g(x) \geq -10$
      have := fin.1
      linarith
      -- $g(x) \leq 4$
      have := fin.2
      linarith
    -- if $y \in [-10, 4]$ then there is some $x$ such that $y = g(x)$
    intro yin
    have ysubin : y - 1 ∈ Set.Icc (-11) 3 := by
      constructor
      have := yin.1
      linarith
      have := yin.2
      linarith
    rw [← hf] at ysubin
    rcases ysubin with ⟨x, hx⟩
    use x / 6
    rw [hg]
    ring_nf
    rw [hx]
    ring