import Mathlib
/- Danielle picks a positive integer $1 \leq n \leq 2016$ uniformly at random. What is the probability that $\operatorname{gcd}(n, 2015)=1$ ? -/
theorem number_theory_609591 : ({a ∈ Finset.range 2017 | Nat.Coprime 2015 a}.card) / (2016 : ℝ) = 1441 / 2016:= by
  -- Prove that 2016 is not in the set of numbers from 0 to 2014 that are coprime to 2015
  have h : 2016 ∉ {a ∈ Finset.range 2015 | Nat.Coprime 2015 a}:= by simp

  -- Show that the set of numbers from 0 to 2016 that are coprime to 2015
  -- equals the set of numbers from 0 to 2014 that are coprime to 2015, plus the element 2016
  have h1 : {a ∈ Finset.range 2017 | Nat.Coprime 2015 a} = Finset.cons 2016 {a ∈ Finset.range 2015 | Nat.Coprime 2015 a} h:= by
    -- Prove this by showing the sets contain the same elements
    ext a
    constructor
    .
      -- Forward direction: if a is in the first set, it's in the second set
      intro h
      simp at h
      simp
      rcases h with ⟨h1, h2⟩
      by_cases h3 : a = 2016
      .
        -- If a = 2016, it's directly in the second set
        left
        exact h3
      .
        -- Otherwise, a is in the range 0 to 2014 and coprime to 2015
        right
        constructor
        .
          -- Prove a < 2015 by contradiction
          by_contra H
          replace h3 : a = 2015:= by omega
          subst a
          simp at h2
        .
          -- a is coprime to 2015
          exact h2
    .
      -- Reverse direction: if a is in the second set, it's in the first set
      intro h
      simp at h
      rcases h with h | h
      .
        -- If a = 2016, show it's in the first set
        simp
        subst a
        simp
        suffices Nat.Coprime 2015 1 by exact this
        simp
      .
        -- Otherwise, a is in range 0 to 2014 and coprime to 2015
        simp
        refine ⟨(by omega), h.2⟩

  -- Apply the previous result
  rw [h1]
  -- Use the formula for the cardinality of a set with one element added
  rw [Finset.card_cons h]
  clear h1 h

  -- Use the totient function to count numbers coprime to 2015
  rw [←Nat.totient_eq_card_coprime 2015]

  -- Calculate the value of Euler's totient function for 2015
  have h : Nat.totient 2015 = 1440:= by
    -- Factor 2015 as 5 * 13 * 31
    rw [show 2015 = 5 * 13 * 31 by omega]
    -- Apply the multiplicative property of the totient function
    rw [Nat.totient_mul (by norm_num)]
    rw [Nat.totient_mul (by norm_num)]
    -- Calculate totient for each prime factor
    rw [Nat.totient_prime (by norm_num)]
    rw [Nat.totient_prime (by norm_num)]
    rw [Nat.totient_prime (by norm_num)]

  -- Substitute the calculated totient value
  rw [h]
  -- Simplify the final expression
  simp
