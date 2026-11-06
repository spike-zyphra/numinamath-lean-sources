import Mathlib
/- $12 \cdot 53$ Consider the equation $\frac{1}{x}+\frac{1}{y}=\frac{1}{p}$ for solutions $(x, y)$, where $x, y$ and $p$ are natural numbers, and $p>1$. Prove that when $p$ is a prime number, the equation has 3 solutions; when $p$ is a composite number, the equation has more than 3 solutions.
(Note: When $a \neq b$, $(a, b)$ and $(b, a)$ are considered different solutions.)
(36th Moscow Mathematical Olympiad, 1973) -/
theorem algebra_157782 (p : ℕ) (h1 : p > 1) : (Nat.Prime p → {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ 1 / (↑x : ℝ) + 1 / (↑y : ℝ) = 1 / (↑p : ℝ)}.ncard = 3) ∧ (¬Nat.Prime p → {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ 1 / (↑x : ℝ) + 1 / (↑y : ℝ) = 1 / (↑p : ℝ)}.encard ≥ 4):= by
  constructor
  -- First part: When p is prime, there are exactly 3 solutions
  .
    intro h
    -- Show that the solution set equals exactly three specific solutions
    have h2 : {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ 1 / (↑x : ℝ) + 1 / (↑y : ℝ) = 1 / (↑p : ℝ)} = {(p + 1, p + p ^ 2), (p + p ^ 2, p + 1), (2 * p, 2 * p)}:= by
      ext ⟨x, y⟩
      constructor
      -- Forward direction: any solution must be one of the three specific solutions
      .
        intro h2
        simp at h2
        rcases h2 with ⟨hx, hy, h2⟩
        -- Prove that x > p (if x ≤ p, then 1/x ≥ 1/p, making the sum too large)
        have g1 : x > p:= by
          by_contra H
          simp at H
          rify at H hx
          replace H : 1 / (↑x : ℝ) ≥ 1 / (↑p : ℝ):= by exact one_div_le_one_div_of_le hx H
          simp at H
          have g2 : (↑(y : ℝ))⁻¹ > 0:= by positivity
          linarith
        -- Similarly prove that y > p
        have g2 : y > p:= by
          by_contra H
          simp at H
          rify at H hy
          replace H : 1 / (↑y : ℝ) ≥ 1 / (↑p : ℝ):= by exact one_div_le_one_div_of_le hy H
          simp at H
          have g3 : (↑(x : ℝ))⁻¹ > 0:= by positivity
          linarith
        -- Clear denominators to get (x + y) * p = x * y
        field_simp at h2
        replace h2 : (x + y) * p = x * y:= by
          rify
          linarith
        -- Substitute x = x1 + p and y = y1 + p where x1, y1 > 0
        set x1:= x - p with hx1
        set y1:= y - p with hy1
        clear_value x1 y1
        replace hx1 : x = x1 + p:= by omega
        replace hy1 : y = y1 + p:= by omega
        subst x y
        -- This gives us x1 * y1 = p²
        replace h2 : x1 * y1 = p * p:= by linarith
        -- Since p is prime and p divides x1 * y1, p must divide x1 or y1
        have h3 : p ∣ x1 * y1:= by rw [h2] ; simp
        replace h3 : p ∣ x1 ∨ p ∣ y1:= by exact (Nat.Prime.dvd_mul h).mp h3
        rcases h3 with h3 | h3
        -- Case 1: p divides x1
        .
          rcases h3 with ⟨k, hk⟩
          subst x1
          -- Then k * y1 = p, and since p is prime, we get the factorizations
          replace h2 : k * y1 = p:= by
            rw [show p * k * y1 = p * (k * y1) by ring] at h2
            replace h1 : p > 0:= by omega
            exact Eq.symm (Nat.eq_of_mul_eq_mul_left h1 (id (Eq.symm h2)))
          have h3 : p ∣ k * y1:= by rw [h2]
          replace h3 : p ∣ k ∨ p ∣ y1:= by exact (Nat.Prime.dvd_mul h).mp h3
          rcases h3 with h3 | h3
          -- Subcase: p divides k
          .
            rcases h3 with ⟨l, hl⟩
            subst k
            replace h2 : l * y1 = 1:= by
              rw [show p * l * y1 = p * (l * y1) by ring] at h2
              replace h1 : p > 0:= by omega
              exact (Nat.mul_right_eq_self_iff h1).mp h2
            simp at h2
            rcases h2 with ⟨g1, g2⟩
            subst l y1
            simp
            right
            left
            ring_nf
            simp
          -- Subcase: p divides y1
          .
            rcases h3 with ⟨l, hl⟩
            subst y1
            replace h2 : l * k = 1:= by
              rw [show k * (p * l) = p * (l * k) by ring] at h2
              replace h1 : p > 0:= by omega
              exact (Nat.mul_right_eq_self_iff h1).mp h2
            simp at h2
            rcases h2 with ⟨g1, g2⟩
            subst l k
            simp
            right
            right
            ring_nf
        -- Case 2: p divides y1 (symmetric to case 1)
        .
          rcases h3 with ⟨k, hk⟩
          subst y1
          replace h2 : x1 * k = p:= by
            rw [show x1 * (p * k) = p * (x1 * k) by ring] at h2
            replace h1 : p > 0:= by omega
            exact Eq.symm (Nat.eq_of_mul_eq_mul_left h1 (id (Eq.symm h2)))
          have h3 : p ∣ x1 * k:= by rw [h2]
          replace h3 : p ∣ x1 ∨ p ∣ k:= by exact (Nat.Prime.dvd_mul h).mp h3
          rcases h3 with h3 | h3
          .
            rcases h3 with ⟨l, hl⟩
            subst x1
            replace h2 : l * k = 1:= by
              rw [show p * l * k = p * (l * k) by ring] at h2
              replace h1 : p > 0:= by omega
              exact (Nat.mul_right_eq_self_iff h1).mp h2
            simp at h2
            rcases h2 with ⟨g1, g2⟩
            subst l k
            simp
            right
            right
            ring_nf
          .
            rcases h3 with ⟨l, hl⟩
            subst k
            replace h2 : x1 * l = 1:= by
              rw [show x1 * (p * l) = p * (x1 * l) by ring] at h2
              replace h1 : p > 0:= by omega
              exact (Nat.mul_right_eq_self_iff h1).mp h2
            simp at h2
            rcases h2 with ⟨g1, g2⟩
            subst x1 l
            simp
            left
            ring_nf
            simp
      -- Backward direction: verify that each of the three solutions works
      .
        intro h2
        simp at h2
        rcases h2 with h2 | h2 | h2
        all_goals
          rcases h2 with ⟨h2, h3⟩
          subst x y
          simp
          constructor
          .
            omega
          .
            field_simp
            ring_nf
    -- Use the characterization to count the solutions
    rw [h2]
    rw [show ({(p + 1, p + p ^ 2), (p + p ^ 2, p + 1), (2 * p, 2 * p)} : Set (ℕ × ℕ)) = ({(p + 1, p + p ^ 2), (p + p ^ 2, p + 1), (2 * p, 2 * p)} : Finset (ℕ × ℕ)) by simp]
    rw [Set.ncard_coe_Finset]
    -- Count the elements in the finite set
    repeat rw [Finset.card_insert_of_not_mem]
    simp
    -- Verify that the elements are distinct
    .
      by_contra H
      simp at H
      replace H:= H.2
      linarith
    .
      by_contra H
      simp at H
      rcases H with H | H
      .
        replace H:= H.1
        nlinarith only [H, h1]
      .
        replace H:= H.1
        linarith
  -- Second part: When p is composite, there are at least 4 solutions
  .
    intro h
    -- Since p is composite and p ≥ 2, there exist proper divisors
    replace h1 : p ≥ 2:= by omega
    have h2:= (Nat.not_prime_iff_exists_dvd_ne h1).1 h
    rcases h2 with ⟨m, hm⟩
    rcases hm with ⟨h2, h3, h4⟩
    rcases h2 with ⟨k, hk⟩
    -- Ensure m > 1 (m is a proper divisor)
    replace h3 : m > 1:= by
      by_contra H
      replace H : m = 0:= by omega
      subst m
      simp at hk
      linarith
    -- Ensure k > 1 (k is also a proper divisor)
    replace h4 : k > 1:= by
      by_contra H
      replace H : k = 0 ∨ k = 1:= by omega
      rcases H with H | H
      .
        subst k
        simp at hk
        linarith
      .
        subst k
        simp at hk
        rw [hk] at h4
        simp at h4
    -- Show that we have at least 4 solutions by exhibiting them
    have h5 : {(p + 1, p + p ^ 2), (p + p ^ 2, p + 1), (p + m, p + k ^ 2 * m), (p + k ^ 2 * m, p + m)} ⊆ {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ 1 / (↑x : ℝ) + 1 / (↑y : ℝ) = 1 / (↑p : ℝ)}:= by
      intro ⟨x, y⟩
      intro h
      simp at h
      rcases h with h | h | h | h
      -- Verify each of the four solutions satisfies the equation
      all_goals
        rcases h with ⟨h1, h2⟩
        subst x y
        simp
      .
        constructor
        .
          left
          linarith
        .
          field_simp
          ring_nf
      .
        constructor
        .
          left
          linarith
        .
          field_simp
          ring_nf
      .
        constructor
        .
          omega
        .
          constructor
          .
            omega
          .
            field_simp
            subst p
            simp
            ring_nf
      .
        constructor
        .
          left
          linarith
        .
          constructor
          .
            left
            linarith
          .
            field_simp
            subst p
            ring_nf
            simp
            ring_nf
    -- Set up notation for the sets
    set A:= {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ 1 / (↑x : ℝ) + 1 / (↑y : ℝ) = 1 / (↑p : ℝ)} with hA
    set B:= ({(p + 1, p + p ^ 2), (p + p ^ 2, p + 1), (p + m, p + k ^ 2 * m), (p + k ^ 2 * m, p + m)} : Finset (ℕ × ℕ)) with hB
    set C:= ({(p + 1, p + p ^ 2), (p + p ^ 2, p + 1), (p + m, p + k ^ 2 * m), (p + k ^ 2 * m, p + m)} : Set (ℕ × ℕ)) with hC
    clear_value A B C
    -- Show that the finite set equals the set version
    have h6 : B = C:= by
      subst B C
      simp
    rw [←h6] at h5
    -- The cardinality of our subset is at most the cardinality of the solution set
    replace h5 : (↑B : Set (ℕ × ℕ)).encard ≤ A.encard:= by exact Set.encard_le_card h5
    -- Show that our subset has exactly 4 elements
    have h7 : (↑B : Set (ℕ × ℕ)).encard = 4:= by
      rw [show (↑B : Set (ℕ × ℕ)).encard = B.card by simp]
      subst B
      -- Count elements by showing they are all distinct
      repeat rw [Finset.card_insert_of_not_mem]
      simp
      -- Verify distinctness of the four solutions
      .
        by_contra H
        simp at H
        rcases H with ⟨H1, H2⟩
        replace H1 : k ^ 2 = 1:= by
          replace h3 : m > 0:= by omega
          exact (Nat.mul_left_eq_self_iff h3).mp H2
        nlinarith only [H1, h4]
      .
        by_contra H
        simp at H
        rcases H with H | H
        .
          replace H:= H.2
          simp at H
          nlinarith only [H, h3, h4]
        .
          replace H:= H.2
          omega
      .
        by_contra H
        simp at H
        rcases H with H | H | H
        .
          replace H:= H.2
          nlinarith only [H, h1]
        .
          replace H:= H.1
          omega
        .
          replace H:= H.1
          nlinarith only [H, h3, h4]
    -- Conclude that the solution set has at least 4 elements
    rw [h7] at h5
    exact h5
