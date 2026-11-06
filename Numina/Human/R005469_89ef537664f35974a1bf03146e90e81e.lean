import Mathlib
/- What is the sum of all integers $x$ such that $|x+2| \leq 10$ ? -/
theorem algebra_608422 (A : Finset ℤ) (hA : A = {x : ℤ | |x + 2| ≤ 10}) : ∑ x in A, x = -42:= by
  -- Proves that set A equals the explicit list of integers from -12 to 8
  have h1 : A = {-12, -11, -10, -9, -8, -7, -6, -5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 7, 8}:= by
    -- Uses extensionality to prove two sets are equal
    ext x
    constructor
    .
      -- Forward direction: if x is in set A, then it's in the explicit list
      intro h
      simp at h
      -- Converts finset membership to set membership
      replace h : x ∈ (↑A : Set ℤ) := by exact h
      rw [hA] at h
      simp at h
      -- Uses properties of absolute value
      have h1 : |x + 2| ≥ x + 2:= by exact le_abs_self (x + 2)
      have h2 : |x + 2| ≥ -(x + 2):= by exact neg_le_abs (x + 2)
      -- Derives bounds for x
      replace h1 : x ≤ 8:= by linarith
      replace h2 : x ≥ -12:= by linarith
      simp
      omega
    .
      -- Backward direction: if x is in the explicit list, then it's in set A
      intro h
      suffices x ∈ (↑A : Set ℤ) by exact this
      fin_cases h
      all_goals
        rw [hA]
        simp
  -- Rewrites set A with explicit list and simplifies to compute the sum
  rw [h1]
  simp
