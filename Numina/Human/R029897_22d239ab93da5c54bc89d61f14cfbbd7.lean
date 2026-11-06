import Mathlib

/- If
\[f(n + 1) = (-1)^{n + 1} n - 2f(n)\]for $n \ge 1,$ and $f(1) = f(1986),$ compute
\[f(1) + f(2) + f(3) + \dots + f(1985).\]-/
theorem algebra_20876 {f : ℕ → ℤ} (h : ∀ n ≥ 1, f (n + 1) = (-1) ^ (n + 1) * n - 2 * f n)
    (h' : f 1 = f 1986) :
    ∑ i in Finset.range 1985, f (i + 1) = 331 := by
  --   We can list the equations
  -- \begin{align*}
  -- f(2) &= 1 - 2f(1), \\
  -- f(3) &= -2 - 2f(2), \\
  -- f(4) &= 3 - 2f(3), \\
  -- f(5) &= -4 - 2f(4), \\
  -- &\dots, \\
  -- f(1985) &= -1984 - 2f(1984), \\
  -- f(1986) &= 1985 - 2f(1985).
  -- \end{align*}Adding these equations, we get
  -- \[f(2) + f(3) + \dots + f(1986) = (1 - 2 + 3 - 4 + \dots + 1983 - 1984 + 1985) - 2f(1) - 2f(2) - \dots - 2f(1985).\]
  have key : ∑ i ∈ Finset.range 1985, ((-1 : ℤ) ^ (i + 1 + 1) * (i + 1) - 2 * f (i + 1)) =
      ∑ i ∈ Finset.range 1985, f (i + 1 + 1) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [h (x + 1) (by omega)]
    congr
  have : ∑ i ∈ Finset.range 1985, f (i + 1 + 1) = ∑ i ∈ Finset.range 1985, f (i + 1) := by
    nth_rw 2 [Finset.sum_range_succ']
    rw [zero_add, h', Finset.sum_range_succ]
  rw [this, Finset.sum_sub_distrib, ← Finset.mul_sum] at key
  --   To find $1 - 2 + 3 - 4 + \dots + 1983 - 1984 + 1985,$ we can pair the terms
  -- \begin{align*}
  -- 1 - 2 + 3 - 4 + \dots + 1983 - 1984 + 1985 &= (1 - 2) + (3 - 4) + \dots + (1983 - 1984) + 1985 \\
  -- &= (-1) + (-1) + \dots + (-1) + 1985 \\
  -- &= -\frac{1984}{2} + 1985 \\
  -- &= 993.
  -- \end{align*}
  have (n : ℕ) : ∑ x ∈ Finset.range (2 * (n + 1)), (-1 : ℤ) ^ (x + 1 + 1) * (↑x + 1) = -(n + 1) := by
    induction' n with n ih
    . norm_num
    rw [show 2 * (n + 1 + 1) = 2 * (n + 1) + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Even.neg_one_pow ⟨n + 2, by ring⟩, Odd.neg_one_pow ⟨n + 2, by ring⟩]
    push_cast
    ring
  rw [Finset.sum_range_succ, show 1984 = 2 * (991 + 1) by norm_num, this] at key
  --   Hence,
  -- \[f(2) + f(3) + \dots + f(1986) = 993 - 2f(1) - 2f(2) - \dots - 2f(1985).\]Then
  -- \[2f(1) + 3f(2) + 3f(3) + \dots + 3f(1985) + f(1986) = 993.\]Since $f(1986) = f(1),$
  -- \[3f(1) + 3f(2) + 3f(3) + \dots + 3f(1985) = 993.\]Therefore, $f(1) + f(2) + f(3) + \dots + f(1985) = \boxed{331}.$
  set s := ∑ i ∈ Finset.range 1985, f (i + 1)
  suffices 993 = 3 * s by linarith
  linear_combination key
