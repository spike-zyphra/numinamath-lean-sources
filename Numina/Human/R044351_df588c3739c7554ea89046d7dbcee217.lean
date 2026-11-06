import Mathlib

/- Let \[f(x) = \left\{
\begin{array}{cl}
\frac{x}{21} & \text{ if }x\text{ is a multiple of 3 and 7}, \\
3x & \text{ if }x\text{ is only a multiple of 7}, \\
7x & \text{ if }x\text{ is only a multiple of 3}, \\
x+3 & \text{ if }x\text{ is not a multiple of 3 or 7}.
\end{array}
\right.\]If $f^a(x)$ means the function is nested $a$ times (for example, $f^2(x)=f(f(x))$), what is the smallest value of $a$ greater than 1 that satisfies $f(2)=f^a(2)$? -/
theorem algebra_456 : let f := fun (x : ℤ) => if x % 3 = 0 ∧ x % 7 = 0 then x / 21 else if x % 7 = 0 then 3 * x else if x % 3 = 0 then 7 * x else x + 3
IsLeast {a | 1 < a ∧ f 2 = f^[a] 2} 7 := by
  rw [IsLeast]
  constructor
  .
    -- proof 7 is belong to ${a | 1 < a ∧ f 2 = f^[a] 2}$
    -- because we need to compute function `f` result, so we use `decide` here
    decide
  .
    rw [lowerBounds]
    simp
    intro a ha h2
    -- we compute $f^{0}(2)$ to $f^{6}(2), all of them cannot satisify our condition, so $a ≥ 7$
    if h : a < 7 then
      rw [← Finset.mem_range] at h
      fin_cases h
      repeat contradiction
    else
      linarith
