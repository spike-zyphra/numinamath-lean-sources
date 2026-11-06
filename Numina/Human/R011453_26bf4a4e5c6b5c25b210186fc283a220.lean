import Mathlib
/- Determine the smallest natural number $n$ for which there exist distinct nonzero naturals $a, b, c$, such that $n=a+b+c$ and $(a + b)(b + c)(c + a)$ is a perfect cube. -/
theorem number_theory_36448 : IsLeast {n : ℕ | ∃ a b c : ℕ, a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ n = a + b + c ∧ (∃ k : ℕ, k ^ 3 = (a + b) * (b + c) * (c + a))} 10:= by
  constructor
  -- First part: Show that 10 is in the set (i.e., 10 satisfies the conditions)
  .
    -- Use a = 7, b = 2, c = 1 as witnesses
    use 7, 2, 1
    simp
    -- Show that (7+2)(2+1)(1+7) = 9*3*8 = 216 = 6^3
    use 6
    simp
  -- Second part: Show that 10 is a lower bound (no smaller number works)
  .
    rw [lowerBounds]
    intro n hn
    -- Extract the existential witnesses from the hypothesis
    rcases hn with ⟨a, b, c, h1, h2, h3, h4, h5, h6, h7, h8⟩
    by_contra H
    simp at H
    -- Extract the cube root k from the perfect cube condition
    rcases h8 with ⟨k, h8⟩
    -- Since n < 10, we have n ∈ {6, 7, 8, 9} (minimum possible is 6 = 1+2+3)
    have h9 : n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9:= by omega
    -- Consider all possible orderings of a, b, c
    have h10 : a < b ∧ b < c ∨ a < c ∧ c < b ∨ b < a ∧ a < c ∨ b < c ∧ c < a ∨ c < a ∧ a < b ∨ c < b ∧ b < a:= by omega
    -- Main lemma: For ordered triples a < b < c, none of the cases n ∈ {6,7,8,9} work
    have h11 : ∀ a b c n k : ℕ, a < b ∧ b < c → a ≠ 0 → b ≠ 0 → c ≠ 0 → a ≠ b → a ≠ c → b ≠ c → n = a + b + c → k ^ 3 = (a + b) * (b + c) * (c + a) → (n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9) → False:= by
      intro a b c n k h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
      rcases h1 with ⟨g1, g2⟩
      rcases h10 with h10 | h10 | h10 | h10
      -- Case n = 6: Only possibility is (1,2,3)
      .
        replace h2 : a = 1:= by omega
        replace h3 : b = 2:= by omega
        replace h4 : c = 3:= by omega
        subst a b c
        simp at h9
        -- For (1,2,3): (1+2)(2+3)(3+1) = 3*5*4 = 60, and 3^3 < 60 < 4^3
        have hk1 : k > 3:= by
          by_contra H
          simp at H
          replace H : k ^ 3 ≤ 3 ^ 3:= by exact Nat.pow_le_pow_of_le_left H 3
          linarith
        have hk2 : k < 4:= by
          by_contra H
          simp at H
          replace H : k ^ 3 ≥ 4 ^ 3:= by exact Nat.pow_le_pow_of_le_left hk1 3
          linarith
        linarith
      -- Case n = 7: Only possibility is (1,2,4)
      .
        replace h2 : a = 1:= by omega
        replace h3 : b = 2:= by omega
        replace h4 : c = 4:= by omega
        subst a b c
        simp at h9
        -- For (1,2,4): (1+2)(2+4)(4+1) = 3*6*5 = 90, and 4^3 < 90 < 5^3
        have hk1 : k > 4:= by
          by_contra H
          simp at H
          replace H : k ^ 3 ≤ 4 ^ 3:= by exact Nat.pow_le_pow_of_le_left H 3
          linarith
        have hk2 : k < 5:= by
          by_contra H
          simp at H
          replace H : k ^ 3 ≥ 5 ^ 3:= by exact Nat.pow_le_pow_of_le_left hk1 3
          linarith
        linarith
      -- Case n = 8: Possibilities are (1,2,5) and (1,3,4)
      .
        have h2 : a = 1:= by omega
        have h3 : b = 2 ∨ b = 3:= by omega
        rcases h3 with h3 | h3
        -- Subcase (1,2,5)
        .
          have h4 : c = 5:= by omega
          subst a b c
          simp at h9
          -- For (1,2,5): (1+2)(2+5)(5+1) = 3*7*6 = 126, and 5^3 < 126 < 6^3
          have hk1 : k > 5:= by
            by_contra H
            simp at H
            replace H : k ^ 3 ≤ 5 ^ 3:= by exact Nat.pow_le_pow_of_le_left H 3
            linarith
          have hk2 : k < 6:= by
            by_contra H
            simp at H
            replace H : k ^ 3 ≥ 6 ^ 3:= by exact Nat.pow_le_pow_of_le_left hk1 3
            linarith
          linarith
        -- Subcase (1,3,4)
        .
          have h4 : c = 4:= by omega
          subst a b c
          simp at h9
          -- For (1,3,4): (1+3)(3+4)(4+1) = 4*7*5 = 140, and 5^3 < 140 < 6^3
          have hk1 : k > 5:= by
            by_contra H
            simp at H
            replace H : k ^ 3 ≤ 5 ^ 3:= by exact Nat.pow_le_pow_of_le_left H 3
            linarith
          have hk2 : k < 6:= by
            by_contra H
            simp at H
            replace H : k ^ 3 ≥ 6 ^ 3:= by exact Nat.pow_le_pow_of_le_left hk1 3
            linarith
          linarith
      -- Case n = 9: Possibilities are (1,2,6), (1,3,5), and (2,3,4)
      .
        replace h1 : a = 1 ∨ a = 2:= by omega
        rcases h1 with h1 | h1
        -- Subcase a = 1
        .
          replace h2 : b = 2 ∨ b = 3:= by omega
          rcases h2 with h2 | h2
          -- Subcase (1,2,6)
          .
            replace h3 : c = 6:= by omega
            subst a b c
            simp at h9
            -- For (1,2,6): (1+2)(2+6)(6+1) = 3*8*7 = 168, and 5^3 < 168 < 6^3
            have hk1 : k > 5:= by
              by_contra H
              simp at H
              replace H : k ^ 3 ≤ 5 ^ 3:= by exact Nat.pow_le_pow_of_le_left H 3
              linarith
            have hk2 : k < 6:= by
              by_contra H
              simp at H
              replace H : k ^ 3 ≥ 6 ^ 3:= by exact Nat.pow_le_pow_of_le_left hk1 3
              linarith
            linarith
          -- Subcase (1,3,5)
          .
            have h4 : c = 5:= by omega
            subst a b c
            simp at h9
            -- For (1,3,5): (1+3)(3+5)(5+1) = 4*8*6 = 192, and 5^3 < 192 < 6^3
            have hk1 : k > 5:= by
              by_contra H
              simp at H
              replace H : k ^ 3 ≤ 5 ^ 3:= by exact Nat.pow_le_pow_of_le_left H 3
              linarith
            have hk2 : k < 6:= by
              by_contra H
              simp at H
              replace H : k ^ 3 ≥ 6 ^ 3:= by exact Nat.pow_le_pow_of_le_left hk1 3
              linarith
            linarith
        -- Subcase (2,3,4)
        .
          replace h2 : b = 3:= by omega
          replace h3 : c = 4:= by omega
          subst a b c
          simp at h9
          -- For (2,3,4): (2+3)(3+4)(4+2) = 5*7*6 = 210, and 5^3 < 210 < 6^3
          have hk1 : k > 5:= by
            by_contra H
            simp at H
            replace H : k ^ 3 ≤ 5 ^ 3:= by exact Nat.pow_le_pow_of_le_left H 3
            linarith
          have hk2 : k < 6:= by
            by_contra H
            simp at H
            replace H : k ^ 3 ≥ 6 ^ 3:= by exact Nat.pow_le_pow_of_le_left hk1 3
            linarith
          linarith
    -- Apply the main lemma to all six possible orderings of a, b, c
    rcases h10 with h10 | h10 | h10 | h10 | h10 | h10
    -- Case: a < b < c
    .
      exact h11 a b c n k h10 h1 h2 h3 h4 h5 h6 h7 h8 h9
    -- Case: a < c < b (reorder to a < c < b)
    .
      exact h11 a c b n k h10 h1 h3 h2 (by omega) (by omega) (by omega) (by linarith) (by linarith) h9
    -- Case: b < a < c (reorder to b < a < c)
    .
      exact h11 b a c n k h10 h2 h1 h3 (by omega) (by omega) (by omega) (by linarith) (by linarith) h9
    -- Case: b < c < a (reorder to b < c < a)
    .
      exact h11 b c a n k h10 h2 h3 h1 (by omega) (by omega) (by omega) (by linarith) (by linarith) h9
    -- Case: c < a < b (reorder to c < a < b)
    .
      exact h11 c a b n k h10 h3 h1 h2 (by omega) (by omega) (by omega) (by linarith) (by linarith) h9
    -- Case: c < b < a (reorder to c < b < a)
    .
      exact h11 c b a n k h10 h3 h2 h1 (by omega) (by omega) (by omega) (by linarith) (by linarith) h9
