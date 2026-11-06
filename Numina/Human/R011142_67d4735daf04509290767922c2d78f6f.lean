import Mathlib
/- Determine all positive integers $x$ for which the expression $x^4 + 4^x - 1$ is a perfect square. -/
theorem number_theory_617916 : {x : ℕ | x > 0 ∧ IsSquare (x ^ 4 + 4 ^ x - 1)} = {1, 3}:= by
  ext x
  constructor
  .
    -- Forward direction: if x > 0 and x^4 + 4^x - 1 is a perfect square, then x ∈ {1, 3}
    intro h
    simp at h
    rcases h with ⟨h1, h2⟩
    -- First, we prove that x must be odd
    have h3 : Odd x:= by
      -- Proof by contradiction: assume x is even
      by_contra H
      simp at H
      rcases h2 with ⟨y, hy⟩
      -- x^4 + 4^x is positive
      have g1 : x ^ 4 + 4 ^ x > 0:= by positivity
      rw [show y * y = y ^ 2 by ring] at hy
      -- Rearrange the equation: x^4 + 4^x = y^2 + 1
      replace hy : x ^ 4 + 4 ^ x = y ^ 2 + 1:= by omega
      -- Show that y must be odd
      have h2 : Odd y:= by
        -- Proof by contradiction: assume y is even
        by_contra H1
        simp at H1
        -- If y is even, then y^2 is even
        replace H1 : Even (y ^ 2):= by refine Even.pow_of_ne_zero H1 (by omega)
        -- So y^2 + 1 is odd
        replace H1 : Odd (y ^ 2 + 1):= by exact Even.add_one H1
        -- 4 is even
        have h2 : Even 4:= by decide
        -- 4^x is even when x > 0
        replace h2 : Even (4 ^ x):= by refine (Nat.even_pow' (by omega)).mpr h2
        -- x^4 is even when x is even
        have h3 : Even (x ^ 4):= by refine Even.pow_of_ne_zero H (by omega)
        -- So x^4 + 4^x is even
        replace h2 : Even (x ^ 4 + 4 ^ x):= by exact Even.add h3 h2
        -- But this contradicts y^2 + 1 being odd
        rw [hy] at h2
        absurd h2
        simp
        exact H1
      -- Since y is odd, write y = 2k + 1
      rcases h2 with ⟨k, hk⟩
      subst y
      -- Show that 4 divides x^4 (since x is even)
      have h2 : 4 ∣ x ^ 4:= by
        rcases H with ⟨t, ht⟩
        subst x
        ring_nf
        omega
      -- 4 divides 4^x
      have h3 : 4 ∣ 4 ^ x:= by refine Dvd.dvd.pow (by omega) (by omega)
      -- So 4 divides x^4 + 4^x
      replace h2 : 4 ∣ x ^ 4 + 4 ^ x:= by exact (Nat.dvd_add_iff_right h2).mp h3
      -- Substitute y = 2k + 1 into the equation
      rw [hy] at h2
      ring_nf at h2
      -- Simplify the expression
      rw [show 2 + k * 4 + k ^ 2 * 4 = 4 * (k ^ 2 + k) + 2 by ring] at h2
      -- 4 divides 4 * (k^2 + k)
      replace h3 : 4 ∣ 4 * (k ^ 2 + k):= by simp
      -- This would imply 4 divides 2, which is impossible
      replace h2 : 4 ∣ 2:= by exact (Nat.dvd_add_iff_right h3).mpr h2
      omega
    -- Since x is odd, write x = 2k + 1
    rcases h3 with ⟨k, hk⟩
    -- Case analysis: check small values of k
    by_cases h4 : k ≤ 6
    .
      -- For k ≤ 6, check each case individually
      replace h4 : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6:= by omega
      rcases h4 with h4 | h4 | h4 | h4 | h4 | h4 | h4
      .
        -- k = 0, so x = 1: this works
        subst k x
        simp
      .
        -- k = 1, so x = 3: this works
        subst k x
        simp
      -- For k = 2, 3, 4, 5, 6 (x = 5, 7, 9, 11, 13): these don't work
      all_goals
        subst k x
        simp at h2
        absurd h2
        native_decide
    .
      -- For k > 6 (x ≥ 15): prove no solutions exist
      simp at h4
      replace hk : x ≥ 15:= by omega
      rcases h2 with ⟨y, hy⟩
      rw [show y * y = y ^ 2 by ring] at hy
      -- Show that y^2 is bounded between (2^x)^2 and (2^x + 1)^2
      -- Lower bound: x^4 + 4^x - 1 > (2^x)^2
      have g1 : x ^ 4 + 4 ^ x - 1 > (2 ^ x) ^ 2:= by
        suffices x ^ 4 + 4 ^ x > (2 ^ x) ^ 2 + 1 by omega
        rw [show 4 ^ x = (2 ^ 2) ^ x by ring]
        rw [show (2 ^ 2) ^ x = 2 ^ (2 * x) by exact Eq.symm (Nat.pow_mul 2 2 x)]
        ring_nf
        suffices x ^ 4 > 1 by omega
        refine Nat.one_lt_pow (by omega) (by omega)
      -- Upper bound: x^4 + 4^x - 1 < (2^x + 1)^2
      have g2 : x ^ 4 + 4 ^ x - 1 < (2 ^ x + 1) ^ 2:= by
        suffices x ^ 4 + 4 ^ x < (2 ^ x + 1) ^ 2 + 1 by omega
        ring_nf
        rw [show 4 ^ x = (2 ^ 2) ^ x by ring]
        rw [show (2 ^ 2) ^ x = 2 ^ (2 * x) by exact Eq.symm (Nat.pow_mul 2 2 x)]
        ring_nf
        suffices x ^ 4 < 2 + 2 * 2 ^ x by linarith
        -- Prove by induction that (x + 15)^4 < 2 * 2^(x + 15) for all x
        have h2 : ∀ x : ℕ, (x + 15) ^ 4 < 2 * 2 ^ (x + 15):= by
          intro x
          induction x with
          | zero =>
            -- Base case: x = 0
            simp
          | succ x hx =>
            -- Inductive step
            rw [show x + 1 + 15 = x + 15 + 1 by ring]
            rw [show 2 ^ (x + 15 + 1) = 2 * 2 ^ (x + 15) by ring]
            suffices (x + 15 + 1) ^ 4 < 2 * (x + 15) ^ 4 by omega
            ring_nf
            omega
        -- Apply the induction result
        specialize h2 (x - 15)
        rw [show x - 15 + 15 = x by omega] at h2
        linarith
      -- This gives us 2^x < y < 2^x + 1, which is impossible for integers
      rw [hy] at g1 g2
      replace g1 : y > 2 ^ x:= by exact lt_of_pow_lt_pow_left' 2 g1
      replace g2 : y < 2 ^ x + 1:= by exact lt_of_pow_lt_pow_left' 2 g2
      linarith
  .
    -- Backward direction: if x ∈ {1, 3}, then x > 0 and x^4 + 4^x - 1 is a perfect square
    intro h
    simp at h
    rcases h with h | h
    -- Check x = 1 and x = 3 by direct computation
    all_goals
      subst x
      simp
      native_decide
