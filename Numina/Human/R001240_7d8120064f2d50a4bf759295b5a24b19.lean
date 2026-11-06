import Mathlib

/- If \[f(x) =
\begin{cases}
2x-5 &\quad \text{if } x \ge 3, \\
-x + 5 &\quad \text{if } x < 3,
\end{cases}
\]then for how many values of $x$ is $f(f(x)) = 3$?-/
theorem algebra_21896 {f : ℝ → ℝ}
    (hf : ∀ x, x ≥ 3 → f x = 2 * x - 5)
    (hf' : ∀ x, x < 3 → f x = -x + 5) :
    {x | f (f x) = 3}.encard = 3 := by
  suffices {x | f (f x) = 3} = {1, 7 / 2, 9 / 2} by
    rw [this, Set.encard_insert_of_not_mem, Set.encard_pair]
    all_goals norm_num
  ext x
  constructor
  swap
  -- Verify that 1, 7/2, 9/2 satisfy $f(f(x))=3$.
  . rintro (rfl | rfl | rfl)
    . simp
      norm_num [hf, hf']
    . simp
      norm_num [hf', hf]
    simp
    norm_num [hf', hf]
  intro hx
  simp at hx ⊢
  -- Let $y = f(x)$. Then, $f(f(x)) = f(y) = 3$,
  set y := f x with hy
  -- so either $2y - 5 = 3$ or $-y + 5 = 3$.
  rcases le_or_lt 3 y with hy3 | hy3
  . -- If $2y - 5 = 3$, then $y = 4$.  Note that $4 \ge 3$, so $f(4) = 3$.
    rw [hf _ hy3] at hx
    replace hx : y = 4 := by linarith
    rw [hy] at hx
    -- Next, we solve the equation $f(x) = 4$.
    -- In this case, either $2x - 5 = 4$ or $-x + 5 = 4$.
    rcases le_or_lt 3 x with hx3 | hx3
    . -- If $2x - 5 = 4$, then $x = 9/2$.  Note that $9/2 \ge 3$, so $f(9/2) = 3$.
      rw [hf _ hx3] at hx
      right; right
      linarith
    -- If $-x + 5 = 4$, then $x = 1$.  Note that $1 < 3$, so $f(1) = 4$.
    rw [hf' _ hx3] at hx
    left
    linarith
  -- If $-y + 5 = 3$, then $y = 2$.  Note that $2 < 3$, so $f(2) = 3$.
  rw [hf' _ hy3] at hx
  replace hx : y = 2 := by linear_combination -hx
  rw [hy] at hx
  -- Now, we solve the equation $f(x) = 2$.
  -- In this case, either $2x - 5 = 2$ or $-x + 5 = 2$.
  rcases le_or_lt 3 x with hx3 | hx3
  . -- If $2x - 5 = 2$, then $x = 7/2$.  Note that $7/2 \ge 3$, so $f(7/2) = 2$.
    rw [hf _ hx3] at hx
    right; left
    linarith
  -- If $-x + 5 = 2$, then $x = 3$.  But $3 \ge 3$, so $f(3) = 2 \cdot 3 - 5 = 1$, which is not 2.
  rw [hf' _ hx3] at hx
  linarith
  -- Therefore, there are $\boxed{3}$ solutions to $f(f(x)) = 3$, namely $x = 1$, 7/2, and 9/2.
