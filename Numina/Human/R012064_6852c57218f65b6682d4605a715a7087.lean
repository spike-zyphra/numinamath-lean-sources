import Mathlib
/- 4. 180 Determine all quadruples $\left(p_{1}, p_{2}, p_{3}, p_{4}\right)$, where $p_{1}, p_{2}, p_{3}, p_{4}$ are all prime numbers, and satisfy:
(1) $p_{1}< p_{2}< p_{3}< p_{4}$;
(2) $p_{1} p_{2}+p_{2} p_{3}+p_{3} p_{4}+p_{4} p_{1}=882$. -/

theorem number_theory_604025 : {(p1, p2, p3, p4) : ℕ × ℕ × ℕ × ℕ | Nat.Prime p1 ∧ Nat.Prime p2 ∧ Nat.Prime p3 ∧ Nat.Prime p4 ∧ p1 < p2 ∧ p2 < p3 ∧ p3 < p4 ∧ p1 * p2 + p2 * p3 + p3 * p4 + p4 * p1 = 882} = {(2, 5, 19, 37), (2, 11, 19, 31), (2, 13, 19, 29)}:= by
  -- Use extensionality to prove set equality
  ext ⟨p1, p2, p3, p4⟩
  constructor
  .
    -- Forward direction: if a quadruple satisfies the conditions, it must be one of the three solutions
    intro h
    simp at h
    -- Extract all the conditions from the hypothesis
    rcases h with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    -- Rewrite the sum as a product: p₁p₂ + p₂p₃ + p₃p₄ + p₄p₁ = (p₁ + p₃)(p₂ + p₄)
    rw [show p1 * p2 + p2 * p3 + p3 * p4 + p4 * p1 = (p1 + p3) * (p2 + p4) by ring_nf] at h8
    -- Prove that p₁ must equal 2
    have g1 : p1 = 2:= by
      -- Proof by contradiction: assume p₁ ≠ 2
      by_contra H
      -- Since p₁ is prime and greater than 1, if p₁ ≠ 2, then p₁ > 2
      have g2 : p1 > 1:= by exact Nat.Prime.one_lt h1
      replace H : p1 > 2:= by omega
      -- All primes except 2 are odd
      have g1 : Odd p1:= by refine Nat.Prime.odd_of_ne_two h1 (by omega)
      replace g2:= Nat.Prime.odd_of_ne_two h2 (by omega)
      have g3 : Odd p3:= by refine Nat.Prime.odd_of_ne_two h3 (by omega)
      have g4 : Odd p4:= by refine Nat.Prime.odd_of_ne_two h4 (by omega)
      -- Sum of two odd numbers is even
      replace g1 : Even (p1 + p3):= by exact Odd.add_odd g1 g3
      replace g2 : Even (p2 + p4):= by exact Odd.add_odd g2 g4
      -- Express even numbers as 2k and 2l
      rcases g1 with ⟨k, hk⟩
      rcases g2 with ⟨l, hl⟩
      rw [hk, hl] at h8
      ring_nf at h8
      -- This would imply 4 divides 882, which is false
      replace h8 : 4 ∣ 882:= by rw [←h8] ; simp
      omega
    -- Substitute p₁ = 2
    subst p1
    clear h1
    -- Use the ordering constraint to bound the sum
    have g1 : 2 + p3 < p2 + p4:= by linarith
    replace g1 : (2 + p3) * (2 + p3) < (p2 + p4) * (2 + p3):= by refine Nat.mul_lt_mul_of_pos_right g1 (by omega)
    rw [show (p2 + p4) * (2 + p3) = 882 by linarith] at g1
    -- This gives us an upper bound: 2 + p₃ < 30
    replace g1 : 2 + p3 < 30:= by
      by_contra H
      simp at H
      replace H : (2 + p3) ^ 2 ≥ 30 ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
      linarith
    -- p₃ is odd (since it's a prime ≠ 2)
    have h1 : Odd p3:= by refine Nat.Prime.odd_of_ne_two h3 (by omega)
    have g2 : Even 2:= by simp
    -- Therefore 2 + p₃ is odd
    replace g2 : Odd (2 + p3):= by exact Even.add_odd g2 h1
    -- Factor 882 = 2 × 441
    rw [show 882 = 2 * 441 by simp] at h8
    -- Since 2 + p₃ is odd and divides 2 × 441, it must divide 441
    have h9 : 2 + p3 ∣ 441:= by
      replace h8 : 2 + p3 ∣ 2 * 441:= by rw [←h8] ; simp
      replace h9 : Nat.Coprime (2 + p3) 2:= by exact Nat.coprime_two_right.mpr g2
      exact Nat.Coprime.dvd_of_dvd_mul_left h9 h8
    -- Compute all divisors of 441
    have h10 : Nat.divisors 441 = {1, 3, 7, 9, 21, 49, 63, 147, 441}:= by native_decide
    replace h9 : 2 + p3 ∈ Nat.divisors 441:= by refine Nat.mem_divisors.mpr ⟨h9, (by omega)⟩
    rw [h10] at h9
    simp at h9
    -- p₂ is odd (since it's a prime ≠ 2)
    have g1 : Odd p2:= by refine Nat.Prime.odd_of_ne_two h2 (by omega)
    -- Express p₂ as 2k + 1
    rcases g1 with ⟨k, hk⟩
    -- Case analysis on all possible values of 2 + p₃
    rcases h9 with h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9 | h9
    .
      -- Case: 2 + p₃ = 1 (impossible since p₃ ≥ 3)
      linarith
    .
      -- Case: 2 + p₃ = 3 (impossible since p₃ ≥ 3)
      linarith
    .
      -- Case: 2 + p₃ = 7, so p₃ = 5
      replace h9 : p3 = 5:= by linarith
      subst p3
      simp at h8
      replace h8 : p2 + p4 = 126:= by linarith
      clear h1 g2 g1
      -- From p₂ = 2k + 1 and the constraint, we get k = 1, so p₂ = 3
      have g1 : k = 1:= by linarith
      subst k
      simp at hk
      subst p2
      -- This gives p₄ = 123, but 123 is not prime
      replace h8 : p4 = 123:= by linarith
      subst p4
      absurd h4
      decide
    .
      -- Case: 2 + p₃ = 9, so p₃ = 7
      replace h9 : p3 = 7:= by linarith
      subst p3
      -- Check possible values of k
      replace g1 : k = 1 ∨ k = 2:= by omega
      rcases g1 with g1 | g1
      .
        -- k = 1 gives p₂ = 3, p₄ = 95 (not prime)
        subst k
        simp at hk
        subst p2
        replace h8 : p4 = 95:= by linarith
        subst p4
        absurd h4
        decide
      .
        -- k = 2 gives p₂ = 5, p₄ = 93 (not prime)
        subst k
        simp at hk
        subst p2
        replace h8 : p4 = 93:= by linarith
        subst p4
        absurd h4
        decide
    .
      -- Case: 2 + p₃ = 21, so p₃ = 19
      replace h9 : p3 = 19:= by linarith
      subst p3
      -- Check all possible values of k
      replace g1 : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8:= by omega
      rcases g1 with g1 | g1 | g1 | g1 | g1 | g1 | g1 | g1
      .
        -- k = 1: p₂ = 3, p₄ = 39 (not prime)
        subst k
        simp at hk
        subst p2
        replace h8 : p4 = 39:= by linarith
        subst p4
        absurd h4
        decide
      .
        -- k = 2: p₂ = 5, p₄ = 37 (prime!) - Valid solution
        subst k
        simp at hk
        subst p2
        replace h8 : p4 = 37:= by linarith
        subst p4
        simp
      .
        -- k = 3: p₂ = 7, p₄ = 35 (not prime)
        subst k
        simp at hk
        subst p2
        replace h8 : p4 = 35:= by linarith
        subst p4
        absurd h4
        decide
      .
        -- k = 4: p₂ = 9 (not prime)
        subst k
        simp at hk
        subst p2
        absurd h2
        decide
      .
        -- k = 5: p₂ = 11, p₄ = 31 (prime!) - Valid solution
        subst k
        simp at hk
        subst p2
        replace h8 : p4 = 31:= by linarith
        subst p4
        simp
      .
        -- k = 6: p₂ = 13, p₄ = 29 (prime!) - Valid solution
        subst k
        simp at hk
        subst p2
        replace h8 : p4 = 29:= by linarith
        subst p4
        simp
      .
        -- k = 7: p₂ = 15 (not prime)
        subst k
        simp at hk
        subst p2
        absurd h2
        decide
      .
        -- k = 8: p₂ = 17, p₄ = 25 (not prime)
        subst k
        simp at hk
        subst p2
        replace h8 : p4 = 25:= by linarith
        subst p4
        absurd h4
        decide
    -- All remaining cases lead to contradictions
    all_goals
      linarith
  -- Backward direction: each of the three solutions satisfies all conditions
  intro h
  simp at h
  -- Case analysis on the three solutions
  rcases h with h | h | h
  all_goals
    -- Extract the values and substitute
    rcases h with ⟨h1, h2, h3, h4⟩
    subst p1 p2 p3 p4
    simp
    -- Verify that all conditions are satisfied (primality, ordering, and equation)
    refine ⟨by decide, by decide, by decide, by decide⟩
