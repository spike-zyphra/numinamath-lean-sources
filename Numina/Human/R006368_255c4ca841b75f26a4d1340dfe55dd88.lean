import Mathlib
/- Let $N$ be a positive integer and $m$ be an integer greater than 1. Let $S$ be the sum of the first $N$ odd positive integers, i.e., $S = 1+3+5+\dots+(2N-1)$. Determine the remainder of $S$ when divided by $m$. Show that this remainder is equal to $N^2 \pmod m$. -/
theorem algebra_636343 (N S : ℕ) (hN : N > 0) (hS : S = ∑ i in Finset.range N, (2 * i + 1)) : S % m = N ^ 2 % m:= by
  -- Prove that the sum of first N odd positive integers equals N^2
  have h1 : ∀ N : ℕ, ∑ i in Finset.range N, (2 * i + 1) = N ^ 2:= by
    -- Introduce arbitrary N
    intro N
    -- Prove by induction on N
    induction N with
    | zero =>
      -- Base case: when N = 0, both sides equal 0
      simp
    | succ N ih =>
      -- Inductive step: assume true for N, prove for N+1
      -- Expand the sum to include the (N+1)th term
      rw [Finset.sum_range_succ]
      -- Use linear arithmetic to complete the proof
      linarith
  -- Apply the lemma h1 to substitute the sum with N^2 in hypothesis hS
  rw [h1 N] at hS
  -- Rewrite the goal using the modified hypothesis
  rw [hS]
