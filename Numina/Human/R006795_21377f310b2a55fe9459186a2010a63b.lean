import Mathlib
/- Let $K$ be a positive integer. Let a sequence $x_n$ be defined by $x_1=4$ and $x_{n+1} = \left(\prod_{i=1}^{n} x_i\right) + K$ for $n \ge 1$.
If $K=21$, find all sets $\{a,b\}$ of two distinct positive integers such that $x_a x_b$ is a perfect square. Show the answer is $\{\{1,2\}, \{1,3\}, \{2,3\}\}$. -/
theorem number_theory_641225 (x : ℕ → ℤ) (h1 : x 1 = 4) (h2 : ∀ n : ℕ, x (n + 2) = (∏ i in Finset.range (n + 1), x (i + 1)) + 21) : {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ a < b ∧ IsSquare (x a * x b)} = {(1, 2), (1, 3), (2, 3)}:= by
  -- Calculate the first few terms of the sequence
  have g1:= h2 0
  have g2:= h2 1
  simp at g1 g2
  rw [h1] at g1
  simp [Finset.prod_range_succ] at g2
  rw [h1, g1] at g2
  simp at g1 g2

  -- Use set extensionality to prove the equality
  ext ⟨a, b⟩
  constructor

  -- Forward direction: if (a,b) is in the left set, then it must be one of the three pairs
  .
    simp
    intro ha hb hab h
    by_contra H
    replace hb : b ≥ 4:= by omega

    -- Prove a recurrence relation for the sequence: x_{n+3} = x_{n+2}^2 - 21*x_{n+2} + 21
    have h3 : ∀ n : ℕ, x (n + 3) = x (n + 2) ^ 2 - 21 * x (n + 2) + 21:= by
      intro n
      induction n with
      | zero =>
        simp [h1, g1, g2]
      | succ n ih =>
        rw [show n + 1 + 3 = n + 2 + 2 by omega]
        have g3:= h2 (n + 2)
        rw [Finset.prod_range_succ] at g3
        have g4:= h2 (n + 1)
        rw [show n + 1 + 1 = n + 2 by omega] at g4
        rw [show n + 1 + 2 = n + 3 by omega] at g4
        replace g4 : x (n + 3) - 21 = ∏ i ∈ Finset.range (n + 2), x (i + 1):= by omega
        rw [←g4] at g3
        ring_nf at g3 ⊢
        linarith

    -- Prove that each term x_{n+1} is coprime with 21
    have h4 : ∀ n : ℕ, ∀ k : ℕ, k ≤ n → IsCoprime (x (k + 1)) 21:= by
      intro n
      induction n with
      | zero =>
        simp [h1]
        norm_num
      | succ n ih =>
        intro k hk
        by_cases h1 : k ≤ n
        .
          exact ih k h1
        .
          replace h : k = n + 1:= by omega
          subst k
          clear h1 hk
          rw [show n + 1 + 1 = n + 2 by omega]
          have g1 : ∀ m : ℕ, m ≤ n → IsCoprime (∏ i ∈ Finset.range (m + 1), x (i + 1)) 21:= by
            intro m hm
            induction m with
            | zero =>
              simp [h1]
              norm_num
            | succ m ih1 =>
              rw [Finset.prod_range_succ]
              specialize ih1 (by omega)
              specialize ih (m + 1) (by omega)
              exact IsCoprime.symm (IsCoprime.mul_right (id (IsCoprime.symm ih1)) (id (IsCoprime.symm ih)))
          specialize g1 n (by omega)
          rw [h2 n]
          rw [show ∏ i ∈ Finset.range (n + 1), x (i + 1) + 21 = ∏ i ∈ Finset.range (n + 1), x (i + 1) + 21 * 1 by simp]
          exact IsCoprime.add_mul_left_left_iff.mpr g1

    -- Simplify to show that x_{n+1} is coprime with 21 for all n
    replace h4 : ∀ n : ℕ, IsCoprime (x (n + 1)) 21:= by
      intro n
      exact h4 n n (by omega)
    have ha1:= h4 (a - 1)
    rw [show a - 1 + 1 = a by omega] at ha1

    -- Prove that x_a divides the product of terms from x_1 to x_{a+n}
    replace h4 : ∀ n : ℕ, x a ∣  ∏ i ∈ Finset.range (a + n), x (i + 1):= by
      intro n
      induction n with
      | zero =>
        simp
        set a1:= a - 1 with ha1
        clear_value a1
        replace ha1 : a = a1 + 1:= by omega
        subst a
        rw [Finset.prod_range_succ]
        simp
      | succ n ih =>
        rw [show a + (n + 1) = a + n + 1 by omega]
        rw [Finset.prod_range_succ]
        rcases ih with ⟨k, hk⟩
        use k * x (a + n + 1)
        rw [hk]
        ring

    -- Prove that x_a and x_b are coprime
    have h5 : IsCoprime (x a) (x b):= by
      set d:= Int.gcd (x a) (x b) with hd
      clear_value d
      suffices d = 1 by subst d ; exact Int.isCoprime_iff_gcd_eq_one.mpr this
      have ga : (↑d : ℤ) ∣ x a:= by
        subst d
        exact Int.gcd_dvd_left
      have gb : (↑d : ℤ) ∣ x b:= by
        subst d
        exact Int.gcd_dvd_right
      specialize h4 (b - a - 1)
      rw [show a + (b - a - 1) = b - 1 by omega] at h4
      specialize h2 (b - 2)
      rw [show b - 2 + 2 = b by omega] at h2
      rw [show b - 2 + 1 = b - 1 by omega] at h2
      rw [h2] at gb
      replace h4 : (↑d : ℤ) ∣ ∏ i ∈ Finset.range (b - 1), x (i + 1):= by exact Int.dvd_trans ga h4
      replace gb : (↑d : ℤ) ∣ 21:= by exact (Int.dvd_iff_dvd_of_dvd_add gb).mp h4
      replace ga : (↑d : ℤ) ∣ Int.gcd (x a) 21:= by exact Int.dvd_gcd ga gb
      replace ha1 : Int.gcd (x a) 21 = 1:= by exact Int.isCoprime_iff_gcd_eq_one.mp ha1
      rw [ha1] at ga
      simp at ga
      replace ga : d ∣ 1:= by
        zify
        exact ga
      simp at ga
      exact ga

    -- Convert to gcd notation
    replace h5 : Int.gcd (x a) (x b) = 1:= by exact Int.isCoprime_iff_gcd_eq_one.mp h5
    rw [show Int.gcd (x a) (x b) = Int.gcd (x b) (x a) by exact Int.gcd_comm (x a) (x b)] at h5

    -- Since x_a * x_b is a perfect square and they are coprime, both must be perfect squares
    rcases h with ⟨k, hk⟩
    rw [show k * k = k ^ 2 by ring] at hk
    rw [show x a * x b = x b * x a by ring] at hk
    have h6:= Int.sq_of_gcd_eq_one h5 hk

    -- Prove that x_{n+3} ≥ 121 for all n
    have h7 : ∀ n : ℕ, x (n + 3) ≥ 121:= by
      intro n
      induction n with
      | zero =>
        simp [g2]
      | succ n ih =>
        rw [show n + 1 + 3 = n + 4 by omega]
        rw [h3 (n + 1)]
        rw [show n + 1 + 2 = n + 3 by omega]
        suffices x (n + 3) * (x (n + 3) - 21) ≥ 100 by linarith
        replace ih : x (n + 3) - 21 ≥ 100:= by linarith
        have h7 : x (n + 3) ≥ 0:= by linarith
        replace h7 : x (n + 3) * (x (n + 3) - 21) ≥ x (n + 3) * 100:= by exact Int.mul_le_mul_of_nonneg_left ih h7
        linarith

    -- Analyze the two cases where x_b is a perfect square
    rcases h6 with ⟨b0, h6⟩
    rcases h6 with h6 | h6
    .
      -- Case 1: x_b = b0^2 where b0 is positive
      specialize h3 (b - 3)
      rw [show b - 3 + 3 = b by omega] at h3
      rw [show b - 3 + 2 = b - 1 by omega] at h3
      specialize h7 (b - 4)
      rw [show b - 4 + 3 = b - 1 by omega] at h7
      have h8 : x b > (x (b - 1) - 11) ^ 2:= by
        rw [h3]
        linarith
      have h9 : x b < (x (b - 1) - 10) ^ 2:= by
        rw [h3]
        linarith
      rw [h6] at h8 h9
      replace h8 : |b0| > |x (b - 1) - 11|:= by exact sq_lt_sq.mp h8
      replace h9 : |b0| < |x (b - 1) - 10|:= by exact sq_lt_sq.mp h9
      rw [show |x (b - 1) - 11| = x (b - 1) - 11 by exact abs_of_pos (by linarith)] at h8
      rw [show |x (b - 1) - 10| = x (b - 1) - 10 by exact abs_of_pos (by linarith)] at h9
      linarith
    .
      -- Case 2: x_b = -b0^2 where b0 is non-zero (contradiction since x_b ≥ 121)
      specialize h7 (b - 3)
      rw [show b - 3 + 3 = b by omega] at h7
      linarith [sq_nonneg b0]

  -- Reverse direction: show that each of the three pairs (1,2), (1,3), (2,3) satisfies the condition
  .
    intro h
    simp at h
    rcases h with h | h | h
    all_goals
      rcases h with ⟨ha, hb⟩
      subst a b
      simp [h1, g1, g2]
      native_decide
