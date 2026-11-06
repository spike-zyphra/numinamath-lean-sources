import Mathlib

/- Let the sequence $(a_n)_{n \ge 1}$ be defined by $a_1 = 3$ and $a_{k+1} = a_k + a_k^2$ for $k \ge 1$.
Let $N$ be an integer such that $N \ge 3$.
Determine the last two digits of $a_N$. Show that the last two digits of $a_N$ are $56$ if $N$ is odd, and $92$ if $N$ is even. -/
theorem number_theory_635679 (a : ℕ → ℕ) (ha₁ : a 1 = 3) (hak : ∀ k ≥ 1, a (k + 1) = a k + a k ^ 2) (N : ℕ) (hN : 3 ≤ N) :
    (a N) % 100 = if Even N then 92 else 56 := by
  -- We use induction on N
  induction N, hN using Nat.le_induction with
  | base =>
    -- Base case, we just compute the first few terms
    norm_num [hak, ha₁, show ¬Even 3 by decide]
  | succ N hN ih =>
    -- Inductive step
    -- We split into even and odd cases
    obtain hNe | hNo := Nat.even_or_odd N
    . -- If N is even, then a N % 100 = 92
      -- (N + 1) is odd(not even)
      -- Simplify using the inductive hypothesis and the recurrence relation
      simp [hNe] at ih
      simp [hak N (Nat.one_le_of_lt hN), Nat.add_mod, Nat.pow_mod, ih, show ¬Even (N + 1) from Nat.not_even_iff_odd.mpr (Even.add_one hNe)]
    . -- If N is odd(not even), then a N % 100 = 56
      -- (N + 1) is even
      -- Simplify using the inductive hypothesis and the recurrence relation
      simp [Nat.not_even_iff_odd.mpr hNo] at ih
      simp [hak N (Nat.one_le_of_lt hN), Nat.add_mod, Nat.pow_mod, ih, show Even (N + 1) from Odd.add_one hNo]