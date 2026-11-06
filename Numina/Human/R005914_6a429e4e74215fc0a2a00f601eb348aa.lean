import Mathlib
/- Suppose $r, s$, and $t$ are nonzero reals such that the polynomial $x^{2}+r x+s$ has $s$ and $t$ as roots, and the polynomial $x^{2}+t x+r$ has 5 as a root. Compute $s$. -/
theorem algebra_610692 (r s t : ℝ) (hr : r ≠ 0) (hs : s ≠ 0) (ht : t ≠ 0) (h1 : ∀ x : ℝ, x ^ 2 + r * x + s = (x - s) * (x - t)) (h2 : 5 ^ 2 + t * 5 + r = 0) : s = 29:= by
    -- Substitute x = 0 into equation h1
    have h3:= h1 0
    -- Substitute x = 1 into equation h1
    have h4:= h1 1
    -- Simplify both equations using ring normalization
    ring_nf at h3 h4
    -- From h4, we get s + r + t = 0
    replace h4 : s + r + t = 0:= by linarith
    -- Solve for t: t = -s - r
    replace h4 : t = -s - r:= by linarith
    -- Substitute the expression for t
    subst t
    -- Simplify equations h2 and h3 using ring normalization
    ring_nf at h2 h3
    -- From h2, solve for r: r = 25/4 - 5s/4
    replace h2 : r = 25 / 4 - 5 / 4 * s:= by linarith
    -- Substitute the expression for r
    subst r
    -- Simplify h3 using ring normalization
    ring_nf at h3
    -- From h3, we get s(s-29) = 0
    replace h3 : s * (s - 29) = 0:= by linarith
    -- Since s ≠ 0 (by hypothesis hs), simplify
    simp [hs] at h3
    -- Therefore s = 29
    linarith
