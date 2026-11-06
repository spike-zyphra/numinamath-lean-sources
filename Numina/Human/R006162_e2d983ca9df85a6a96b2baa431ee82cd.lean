import Mathlib

/-
Theorem number_theory_182: Distribution of Apples Problem
If the number of people is n, then the total number of apples distributed is the sum of the first n natural numbers: 1 + 2 + ... + n. This sum is given by n(n+1)/2. We need to find the largest n such that n(n+1)/2 ≤ 100.
-/
theorem number_theory_182 
    (a n : ℕ) 
    (h1 : a = ∑ i ∈ Finset.range (n + 1) , i)
    (h2 : a ≤ 100) :
    n ≤ 13 := by

  -- The sum of the first n natural numbers is given by the formula n(n+1)/2
  have h3: ∑ i ∈ Finset.range (n + 1) , i = n * (n + 1) / 2 := by
    rw [Finset.sum_range_id]
    simp [Nat.mul_add, Nat.add_mul, Nat.pow_two]

  -- Substitute the formula into the inequality a ≤ 100
  rw [h1, h3] at h2

  -- Prove by contradiction that n must be ≤ 13
  have h4 : n ≤ 13 := by
    by_contra h

    -- If n is not ≤ 13, then n ≥ 14
    have h5 : n ≥ 14 := by omega

    -- Show that if n ≥ 14, then the sum n(n+1)/2 exceeds 100
    have h6 : n * (n + 1) / 2 > 100 := by

      -- Since n ≥ 14, n(n+1) ≥ 14*15
      have h7 : n * (n + 1) ≥ 14 * 15 := by
        nlinarith

      -- Therefore, n(n+1)/2 ≥ 14*15/2
      have h8 : n * (n + 1) / 2 ≥ 14 * 15 / 2 := by
        omega

      -- Calculate 14*15/2 = 105, which is > 100
      have h9 : 14 * 15 / 2 > 100 := by norm_num
      omega
      
    -- This contradicts the assumption that a ≤ 100
    omega
  exact h4
