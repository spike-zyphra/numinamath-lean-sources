import Mathlib
/- Determine the value of

$$
2002+\frac{1}{2}\left(2001+\frac{1}{2}\left(2000+\cdots+\frac{1}{2}\left(3+\frac{1}{2} \cdot 2\right)\right) \cdots\right) .
$$ -/
theorem algebra_610979 (a : ℕ → ℝ) (h : a 0 = 2) (hn : ∀ n : ℕ, a (n + 1) = n + 3 + 1 / 2 * a n) : a 2000 = 4002:= by
  -- Define a helper lemma h1: for all n, a n = 2 * (n + 1)
  have h1 : ∀ n : ℕ, a n = 2 * (n + 1):= by
    -- Introduce n for induction
    intro n
    -- Start induction on n
    induction n with
    | zero =>
      -- Base case: when n = 0, simplify using the initial condition h
      simp [h]
    | succ n ih =>
      -- Inductive step: assume the hypothesis holds for n, prove for n + 1
      rw [hn n, ih]
      -- Simplify the expression
      simp
      -- Use linear arithmetic to conclude the step
      linarith
  -- Apply the helper lemma to n = 2000
  specialize h1 2000
  -- Normalize the expression
  ring_nf at h1
  -- Conclude the proof by exacting h1
  exact h1
