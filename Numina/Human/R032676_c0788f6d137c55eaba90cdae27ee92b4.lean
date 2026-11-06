import Mathlib
/- Pour un réel $x$, on note $\lfloor x\rfloor$ le plus grand entier relatif inférieur ou égal à $x$ (par exemple, $\lfloor 2,7\rfloor=2,\lfloor\pi\rfloor=3$ et $\lfloor-1,5\rfloor=-2)$.
Soient $a, b$ deux réels tels que

$$
a+\lfloor a\rfloor=b+\lfloor b\rfloor .
$$

Montrer que $a=b$. -/
theorem algebra_607356 {a b : ℝ} (ha : a + ⌊a⌋ = b + ⌊b⌋) : a = b := by
  -- Proof by contradiction
  by_contra h
  -- If a ≠ b, then either a < b or a > b
  replace h : a < b ∨ a > b:= by exact lt_or_gt_of_ne h
  rcases h with h | h
  . -- Case 1: a < b
    -- If a < b, then floor(a) ≤ floor(b)
    have h1 : ⌊a⌋ ≤ ⌊b⌋:= by refine Int.floor_le_floor (by linarith)
    rify at h1
    linarith
  . -- Case 2: a > b
    -- If a > b, then floor(b) ≤ floor(a)
    have h1 : ⌊b⌋ ≤ ⌊a⌋:= by refine Int.floor_le_floor (by linarith)
    rify at h1
    linarith
