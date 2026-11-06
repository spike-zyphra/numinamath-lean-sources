import Mathlib
/- Determine the value of

$$
1 \cdot 2-2 \cdot 3+3 \cdot 4-4 \cdot 5+\cdots+2001 \cdot 2002 .
$$ -/
theorem algebra_611067 : ∑ i in Finset.range 2001, ((-1 : ℝ) ^ i * (i + 1) * (i + 2)) = 2004002:= by

  -- Helper lemma: For any natural number n, the sum up to (2n+1) terms equals 2(n+1)²
  have h1 : ∀ n : ℕ, ∑ i in Finset.range (2 * n + 1), ((-1 : ℝ) ^ i * (i + 1) * (i + 2)) = 2 * (n + 1) ^ 2:= by
    intro n
    induction n with
    | zero =>
      -- Base case: n = 0
      simp
    | succ n ih =>
      -- Inductive step: prove for n+1 using the inductive hypothesis
      simp
      -- Rewrite 2(n+1)+1 as (2n+1)+2 for easier manipulation
      rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by omega]
      -- Split the sum at the last two terms
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [ih]
      -- Prove that 2n+1 is odd and 2n+2 is even
      have g1 : Odd (2 * n + 1):= by simp
      have g2 : Even (2 * n + 2):= by rw [show 2 * n + 2 = 2 * (n + 1) by omega] ; simp
      -- Use these facts to simplify (-1)^(2n+1) and (-1)^(2n+2)
      rw [show (-1 : ℝ) ^ (2 * n + 1) = -1 by exact Odd.neg_one_pow g1]
      rw [show (-1 : ℝ) ^ (2 * n + 2) = 1 by exact Even.neg_one_pow g2]
      simp
      linarith

  -- Apply the helper lemma with n = 1000 to get our result
  specialize h1 1000
  -- Show that 2*1000 + 1 = 2001
  rw [show 2 * 1000 + 1 = 2001 by omega] at h1
  rw [h1]
  -- Compute the final numerical result
  norm_num
