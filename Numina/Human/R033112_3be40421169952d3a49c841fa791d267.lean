import Mathlib
/- For how many integers $n$ between 1 and 2005 , inclusive, is $2 \cdot 6 \cdot 10 \cdots(4 n-2)$ divisible by $n!$ ? -/
theorem number_theory_611356 : {n : ℕ | 1 ≤ n ∧ n ≤ 2005 ∧ Nat.factorial n ∣ ∏ i in Finset.range n, (4 * i + 2)}.ncard = 2005:= by
  -- First, we prove a key identity: ∏(4i+2) = (2n choose n) * n!
  have g1 : ∀ n : ℕ, ∏ i in Finset.range n, (4 * i + 2) = Nat.choose (2 * n) n * Nat.factorial n:= by
    intro n
    induction n with
    -- Base case: n = 0
    | zero =>
      simp
    -- Inductive step: assume true for n, prove for n+1
    | succ n ih =>
      rw [Finset.prod_range_succ, ih]
      -- Using the binomial coefficient identity: (2n choose n) * n! * n! = (2n)!
      have h1 : (2 * n).choose n * n.factorial * (2 * n - n).factorial = (2 * n).factorial:= by exact Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by linarith)
      -- Similar identity for n+1
      have h2 : (2 * (n + 1)).choose (n + 1) * (n + 1).factorial * (2 * (n + 1) - (n + 1)).factorial = (2 * (n + 1)).factorial:= by exact Nat.choose_mul_factorial_mul_factorial (show n + 1 ≤ 2 * (n + 1) by linarith)
      -- Simplify expressions
      rw [show 2 * n - n = n by omega] at h1
      rw [show 2 * (n + 1) - (n + 1) = n + 1 by omega] at h2
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega] at h2
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
      -- Convert to real numbers for algebraic manipulation
      rify at h1 h2
      -- Rewrite binomial coefficients in terms of factorials
      replace h1 : (↑((2 * n).choose n) : ℝ) = ↑(2 * n).factorial / (n.factorial ^ 2):= by
        field_simp
        linarith
      replace h2 : (↑((2 * n + 1 + 1).choose (n + 1)) : ℝ) = ↑(2 * n + 1 + 1).factorial / ((n + 1).factorial ^ 2):= by
        field_simp
        linarith
      -- Convert back to natural numbers and complete the proof
      rify
      rw [h1, h2]
      field_simp
      repeat rw [Nat.factorial_succ]
      simp
      linarith

  -- Now we prove that the set of n where n! divides the product equals exactly the integers from 1 to 2005
  have h1 : {n : ℕ | 1 ≤ n ∧ n ≤ 2005 ∧ Nat.factorial n ∣ ∏ i in Finset.range n, (4 * i + 2)} = Set.Icc 1 2005:= by
    ext n
    constructor
    -- Forward direction: if n is in our set, then 1 ≤ n ≤ 2005
    .
      intro h
      simp at h
      rcases h with ⟨h1, h2, _⟩
      simp
      exact ⟨h1, h2⟩
    -- Reverse direction: if 1 ≤ n ≤ 2005, then n! divides the product
    .
      intro h
      simp at h
      rcases h with ⟨h1, h2⟩
      simp
      refine ⟨h1, h2, ?_⟩
      -- Use our earlier identity to show divisibility
      .
        specialize g1 n
        rw [g1]
        simp

  -- Apply our set equality and count the elements
  rw [h1]
  clear h1 g1
  -- Convert from Set to Finset for counting
  rw [show (Set.Icc 1 2005 : Set ℕ) = ((Finset.Icc 1 2005) : Finset ℕ) by simp]
  rw [Set.ncard_coe_Finset]
  -- The cardinality of integers from 1 to 2005 is 2005
  rw [Nat.card_Icc 1 2005]
