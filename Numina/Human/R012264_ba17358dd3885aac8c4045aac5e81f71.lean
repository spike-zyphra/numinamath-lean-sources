import Mathlib

/- What is the largest natural number $k$ for which there are infinitely many sequences of $k$ consecutive natural numbers, each of which can be written as the sum of two square numbers? (0 is also considered a square number.) -/
theorem number_theory_197053 (k : ℕ) :
    (∀ n, ∃ m, m > n ∧ ∀ i ∈ Finset.range k, ∃ a b, a^2 + b^2 = m + i) ↔
    k ≤ 3 := by
    constructor
    contrapose!
    -- Among any four consecutive integers, one is congruent to 3 modulo 4
    intro h_kgt3
    use 0
    intro m h_mpos
    -- In particular, m + (3 - m % 4) is congruent to 3 modulo 4
    -- We will show that this implies that m + (3 - m % 4) is not a sum of two squares
    use 3 - m % 4
    constructor
    apply Finset.mem_range.mpr
    suffices: 3 - m % 4 ≤ 3
    linarith; omega
    have h_mod: (m + (3 - m % 4)) % 4 = 3 := by omega
    -- The sum of two squares is never congruent to 3 modulo 4
    have sum_sq_mod_4: ∀ a b, (a^2 + b^2) % 4 ≠ 3 := by
      intro a b
      -- Suffices to consider the possible remainders of a and b modulo 4
      have: (a^2 + b^2) % 4 = ((a % 4)^2 + (b % 4)^2) % 4 := by simp [Nat.pow_mod, Nat.add_mod]
      rw [this]
      have: a%4 < 4 := by simp [Nat.mod_lt]
      have: b%4 < 4 := by simp [Nat.mod_lt]
      interval_cases ha: (a % 4)
      all_goals interval_cases hb: (b % 4)
      all_goals simp
    intro a b
    by_contra h_eq
    -- If m + (3 - m % 4) were a sum of two squares, we would have two squares that
    -- sum to 3 modulo 4
    have: (a^2 + b^2) % 4 = (m + (3 - m%4)) % 4 := by rw [h_eq]
    rw [h_mod] at this
    have := sum_sq_mod_4 a b
    contradiction
    intro h_kle3 n
    -- We will show that 3^2^n - 1, 3^2^n, 3^2^n + 1 are three consecutive integers
    -- that are each a sum of two squares
    use 3^2^(n + 1) - 1
    constructor
    -- We show that 3^2^n - 1 can be made arbitrarily large, which establishes
    -- that infinitely many of the desired triples exist
    induction' n with n hn
    decide
    let m := 3^2^(n + 1)
    calc
      3^2^(n + 1 + 1) - 1 = m * (m - 1) + (m - 1) := by
        unfold m; zify; simp; ring
      _ > m * n + (m - 1) := by
        have: m * (m - 1) > m * n := by
          apply Nat.mul_lt_mul_of_pos_left hn
          apply Nat.pow_pos (by decide)
        exact Nat.add_lt_add_right this (m - 1)
      _ ≥ n + 1 := by omega
    intro i h_imem
    rw [Finset.mem_range] at h_imem
    have: i < 3 := by linarith
    -- We show that m, m + 1, and m + 2 are each a sum of two squares
    match i with
    | 0 =>
      -- We show by induction that 3^2^n - 1 is a sum of two squares. It is easier to
      -- establish the result for integers because subtraction is then well-behaved
      have two_squares: ∀ s, ∃ a b : ℤ, a^2 + b^2 = 3^2^s - 1 := by
        intro s
        induction' s with s hs
        use 1, 1; rfl
        match s with
        | 0 =>
          use 2, 2; rfl
        | t + 1 =>
          let ⟨a, b, h_ab⟩ := hs
          -- We use the identity (a^2 + b^2)(x^2 + y^2) = (ax + by)^2 + (bx - ay)^2
          -- With a and b from the induction hypothesis, and x = 3^2^t, y = 1
          -- to obtain 3^2^(t + 1) - 1 = (3^2^t - 1)(3^2^t + 1) as a sum of squares
          use 3^2^t * a + b
          use 3^2^t * b - a
          ring_nf
          have: a^2 = 3^2^(t + 1) - 1 - b^2 := by linarith
          repeat rw [this]
          ring
      let ⟨a, b, h_ab⟩ := two_squares (n + 1)
      use a.natAbs, b.natAbs
      zify
      simp [h_ab]
    | 1 =>
      -- 3^2^(n + 1) is already a square, so we use 0 for the second square in the sum
      use 3^2^n, 0
      rw [Nat.sub_add_cancel]; ring
      apply Nat.one_le_pow; decide
    | 2 =>
      -- And we can add 1 which is also a square
      use 3^2^n, 1
      simp
      rw [Nat.sub_add_cancel]; ring
      apply Nat.one_le_pow; decide