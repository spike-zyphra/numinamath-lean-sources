import Mathlib

/- 11. Determine the largest even positive integer which cannot be expressed as the sum of two composite odd positive integers.-/

  -- Helper lemma: any multiple of 3 greater than 3 is not prime
lemma three_divides_not_prime (n : ℕ) : 3 ∣ n ∧ n > 3 → ¬Nat.Prime n := by
  rintro ⟨⟨k, rfl⟩, h⟩
  apply Nat.not_prime_mul
  · norm_num  -- proves 3 > 1
  · omega     -- proves k > 1 (since n > 3)

theorem number_theory_100604 : IsGreatest {n | Even n ∧ ¬ ∃ a b, a + b = n ∧ (Odd a ∧ ¬Nat.Prime a) ∧ (Odd b ∧ ¬Nat.Prime b)} 38 := by

  -- Main construction: for n > 38, we can find two composite odd numbers that sum to n
  have n_gt_38_is_odd_composite (n : ℕ) (h : n > 38) (he : Even n) : ∃ p q, p + q = n ∧ (Odd p ∧ ¬Nat.Prime p) ∧ (Odd q ∧ ¬Nat.Prime q) := by
    -- Key divisibility fact: for any n, one of n-15, n-25, or n-35 must be divisible by 3
    have (n : ℕ) : 3 ∣ (n - 15) ∨ 3 ∣ (n - 25) ∨ 3 ∣ (n - 35) := by
      omega  -- automatic arithmetic solver handles this divisibility property
    
    -- Case analysis based on which term is divisible by 3
    rcases this n with hn' | hn' | hn'
    
    -- Case 1: n-15 is divisible by 3
    · use 15, n - 15
      constructor
      · omega  -- proves 15 + (n-15) = n
      · constructor
        · constructor <;> decide  -- proves 15 is odd and composite
        · constructor
          -- Prove n-15 is odd
          · refine (Nat.odd_sub' ?_).mpr ?_
            linarith  -- handles inequalities
            constructor <;> intro h
            · exact he  -- n is even
            · decide   -- 15 is odd
          -- Prove n-15 is composite
          · apply three_divides_not_prime
            omega  -- proves divisibility and n-15 > 3
    
    -- Case 2: n-25 is divisible by 3 (similar to case 1)
    · use 25, n - 25
      constructor
      · omega
      · constructor
        · constructor <;> decide  -- 25 is odd and composite
        · constructor
          · refine (Nat.odd_sub' ?_).mpr ?_
            linarith
            constructor <;> intro h
            · exact he
            · decide
          · apply three_divides_not_prime
            omega
    
    -- Case 3: n-35 is divisible by 3 (similar to case 1)
    · use 35, n - 35
      constructor
      · omega
      · constructor
        · constructor <;> decide  -- 35 is odd and composite
        · constructor
          · refine (Nat.odd_sub' ?_).mpr ?_
            linarith
            constructor <;> intro h
            · exact he
            · decide
          · apply three_divides_not_prime
            omega

  -- Now prove that 38 is the greatest number satisfying the condition
  constructor
  · -- First show 38 is in the set
    constructor
    · use 19  -- prove 38 is even by showing it's 2*19
    · -- Show 38 can't be expressed as sum of two composite odds
      intro h
      obtain ⟨a, b, hab, ⟨ha1, ha2⟩ , ⟨hb1, hb2⟩⟩ := h
      have : a ≤ 38:= by omega
      have : b ≤ 38 := by omega
      have hb : b = 38 - a := by omega
      -- Exhaustively check all possible a values from 1 to 38
      (interval_cases a) <;> (simp at hb; rw [hb] at hb1; rw [hb] at hb2) <;> contradiction
  · -- Show any larger even number can be expressed this way
    intro n ⟨hn_even, hn_gt⟩
    by_contra hn
    apply hn_gt
    apply n_gt_38_is_odd_composite
    omega       -- proves n > 38 from the contradiction hypothesis
    exact hn_even
  