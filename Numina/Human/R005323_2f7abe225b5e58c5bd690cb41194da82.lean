import Mathlib
/- Déterminer tous les entiers naturels a pour lesquels il existe des nombres premiers $\mathbf{p}, \mathbf{q}, \mathrm{r}$, pas forcément distincts, tels que

$$
a=\frac{p+q}{r}+\frac{q+r}{p}+\frac{r+p}{q}
$$ -/
theorem number_theory_607639 (a : ℕ) : (∃ p q r : ℕ, p.Prime ∧ q.Prime ∧ r.Prime ∧
(↑a : ℝ) = (p + q) / r + (q + r) / p + (r + p) / q) ↔ a = 6:= by
  constructor
  -- Forward direction: if such primes exist, then a = 6
  .
    intro h
    rcases h with ⟨p, q, r, hp, hq, hr, h⟩
    -- Establish that p, q, r > 1 since they are prime
    have hp1:= Nat.Prime.one_lt hp
    have hq1:= Nat.Prime.one_lt hq
    have hr1:= Nat.Prime.one_lt hr
    field_simp at h
    -- Rearrange the equation to eliminate fractions
    replace h : a * (r * p * q) = ((p + q) * p + (q + r) * r) * q + (r + p) * (r * p):= by rify ; exact h
    -- Case analysis: either some of p, q, r are equal, or they are all different
    by_cases h1 : p = q ∨ q = r ∨ r = p
    -- Case 1: At least two of p, q, r are equal
    .
      -- This helper lemma handles the case where p = q
      have h3 : ∀ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r → p = q → (p ≠ q ∨ q ≠ r ∨ r ≠ p) → a * (r * p * q) = ((p + q) * p + (q + r) * r) * q + (r + p) * (r * p) → False:= by
        intro p q r ⟨hp, hq, hr⟩ h1 hne h
        subst p
        have hq1:= Nat.Prime.one_lt hq
        rw [show a * (r * q * q)  = r * (a * q * q) by ring] at h
        -- Show that r divides the right side of the equation
        have h1 : r ∣ ((q + q) * q + (q + r) * r) * q + (r + q) * (r * q):= by rw [←h] ; simp
        rw [show ((q + q) * q + (q + r) * r) * q + (r + q) * (r * q) = 2 * q ^ 3 + r * (2 * q * (q + r)) by ring] at h1
        have h2 : r ∣ r * (2 * q * (q + r)):= by simp
        -- r divides 2*q^3
        replace h1 : r ∣ 2 * q ^ 3:= by exact (Nat.dvd_add_iff_left h2).mpr h1
        -- r divides 2 or r divides q^3
        replace h1 : r ∣ 2 ∨ r ∣ q ^ 3:= by exact (Nat.Prime.dvd_mul hr).mp h1
        rcases h1 with h1 | h1
        -- Case: r divides 2
        .
          have g1 : Nat.Prime 2:= by norm_num
          replace h1 : r = 1 ∨ r = 2:= by exact (Nat.dvd_prime g1).mp h1
          rcases h1 with h1 | h1
          -- r cannot be 1 since it's prime
          .
            have g2:= Nat.Prime.one_lt hr
            linarith
          -- Case: r = 2
          .
            subst r
            ring_nf at h
            -- Simplify the equation with r = 2
            replace h : a * q = 4 + 2 * q + q ^ 2:= by
              zify
              zify at h
              replace h : (q : ℤ) * (a * q - (4 + 2 * q + q ^ 2)) = 0:= by linarith
              simp at h
              rcases h with h | h
              all_goals
                linarith
            -- q divides the right side
            replace h : q ∣ 4 + 2 * q + q ^ 2:= by rw [←h] ; simp
            have g2 : q ∣ q ^ 2:= by exact Dvd.intro_left (q.pow 1) rfl
            replace h : q ∣ 4 + 2 * q:= by exact (Nat.dvd_add_iff_left g2).mpr h
            have g3 : q ∣ 2 * q:= by simp
            -- q divides 4
            replace h : q ∣ 4:= by exact (Nat.dvd_add_iff_left g3).mpr h
            rw [show 4 = 2 ^ 2 by ring] at h
            -- q divides 2
            replace h : q ∣ 2:= by exact Nat.Prime.dvd_of_dvd_pow hq h
            replace h : q = 1 ∨ q = 2:= by exact (Nat.dvd_prime g1).mp h
            rcases h with h | h
            -- q cannot be 1 since it's prime
            .
              linarith
            -- Case: q = 2
            .
              subst q
              simp at hne
        -- Case: r divides q^3
        replace h1 : r ∣ q:= by exact Nat.Prime.dvd_of_dvd_pow hr h1
        replace h1 : r = 1 ∨ r = q:= by exact (Nat.dvd_prime hq).mp h1
        rcases h1 with h1 | h1
        -- r cannot be 1 since it's prime
        .
          have hr1:= Nat.Prime.one_lt hr
          linarith
        -- Case: r = q
        .
          subst r
          simp at hne
      -- Check if all three primes are equal
      by_cases h2 : ¬(p = q ∧ q = r)
      -- Case: not all three are equal, but at least two are
      .
        rcases h1 with h1 | h1 | h1
        -- Case: p = q
        .
          specialize h3 p q r ⟨hp, hq, hr⟩ h1 (by aesop) h
          trivial
        -- Case: q = r
        .
          specialize h3 q r p ⟨hq, hr, hp⟩ h1 (by aesop) (by linarith only [h])
          trivial
        -- Case: r = p
        .
          specialize h3 r p q ⟨hr, hp, hq⟩ h1 (by aesop) (by linarith only [h])
          trivial
      -- Case: all three primes are equal (p = q = r)
      .
        simp at h2
        rcases h2 with ⟨h2, h4⟩
        subst q p
        ring_nf at h
        zify at h
        -- Simplify to show that a must be 6
        replace h : (↑r : ℤ) ^ 3 * (a - 6) = 0:= by linarith
        simp at h
        zify
        rcases h with h | h
        all_goals
          linarith
    -- Case 2: All p, q, r are different
    .
      simp at h1
      -- One of the primes must be strictly larger than the other two
      replace h1 : (p > q ∧ p > r) ∨ (q > r ∧ q > p) ∨ (r > p ∧ r > q):= by
        rcases h1 with ⟨h1, h2, h3⟩
        replace h1:= Nat.lt_or_gt_of_ne h1
        replace h2:= Nat.lt_or_gt_of_ne h2
        replace h3:= Nat.lt_or_gt_of_ne h3
        rcases h1 with h1 | h1
        all_goals
          rcases h2 with h2 | h2
          all_goals
            rcases h3 with h3 | h3
            any_goals
              tauto
            all_goals
              linarith
        all_goals
          linarith
      -- Helper lemma for the case where p is the largest prime
      have h2 : ∀ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r → (p > q ∧ p > r) → a * (r * p * q) = ((p + q) * p + (q + r) * r) * q + (r + p) * (r * p) → False:= by
        intro p q r ⟨hp, hq, hr⟩ ⟨h1, h2⟩ h
        have hp1:= Nat.Prime.one_lt hp
        -- p cannot be 2 since it's larger than other primes
        have h3 : p ≠ 2:= by
          by_contra H
          have g1:= Nat.Prime.one_lt hq
          linarith
        -- p must be odd
        replace h3 : Odd p:= by exact Nat.Prime.odd_of_ne_two hp h3
        rw [show a * (r * p * q) = p * (a * q * r) by ring] at h
        rw [show ((p + q) * p + (q + r) * r) * q + (r + p) * (r * p) = r * q * (r + q) + p * (q * (p + q) + r * (p + r)) by ring] at h
        have g:= h
        -- p divides the right side
        replace h : p ∣ r * q * (r + q) + p * (q * (p + q) + r * (p + r)):= by rw [←h] ; simp
        have h4 : p ∣ p * (q * (p + q) + r * (p + r)):= by simp
        -- p divides r * q * (r + q)
        replace h : p ∣ r * q * (r + q):= by exact (Nat.dvd_add_iff_left h4).mpr h
        -- p divides r*q or p divides r+q
        replace h : p ∣ r * q ∨ p ∣ r + q:= by exact (Nat.Prime.dvd_mul hp).mp h
        rcases h with h | h
        -- Case: p divides r*q
        .
          replace h : p ∣ r ∨ p ∣ q:= by exact (Nat.Prime.dvd_mul hp).mp h
          rcases h with h | h
          -- Case: p divides r
          .
            replace h : p = 1 ∨ p = r:= by exact (Nat.dvd_prime hr).mp h
            rcases h with h | h
            all_goals
              linarith
          -- Case: p divides q
          .
            replace h : p = 1 ∨ p = q:= by exact (Nat.dvd_prime hq).mp h
            rcases h with h | h
            all_goals
              linarith
        -- Case: p divides r+q
        .
          replace h : ∃ k : ℕ, r + q = p * k:= by exact h
          rcases h with ⟨k, h⟩
          -- k must be at least 1
          have hk1 : k ≥ 1:= by
            by_contra H
            simp at H
            subst k
            simp at h
            have hq1:= Nat.Prime.one_lt hq
            replace h:= h.2
            linarith
          -- k must be at most 1
          have hk2 : k ≤ 1:= by
            by_contra H
            simp at H
            replace H : k ≥ 2:= by linarith
            replace H : p * k ≥ p * 2:= by exact Nat.mul_le_mul_left p H
            linarith
          -- k must be exactly 1
          replace hk1 : k = 1:= by linarith
          subst k
          simp at h
          -- Check if either r or q is 2
          by_cases h5 : r = 2 ∨ q = 2
          -- Case: either r or q is 2
          .
            rcases h5 with h5 | h5
            -- Case: r = 2
            .
              subst r
              rw [←h] at g
              ring_nf at g
              rw [show q * a * 4 + q ^ 2 * a * 2 = q * (a * 4 + q * a * 2) by ring] at g
              rw [show 16 + q * 20 + q ^ 2 * 10 + q ^ 3 * 2 = 2 ^ 4 + q * (20 + q * (10 + q * 2)) by ring] at g
              have g1 : q ∣ q * (a * 4 + q * a * 2):= by simp
              rw [g] at g1
              have g2 : q ∣ q * (20 + q * (10 + q * 2)):= by simp
              -- q divides 2^4
              replace g1 : q ∣ 2 ^ 4:= by exact (Nat.dvd_add_iff_left g2).mpr g1
              -- q divides 2
              have g3 : q ∣ 2:= by exact Nat.Prime.dvd_of_dvd_pow hq g1
              replace g3 : q = 1 ∨ q = 2:= by exact (Nat.dvd_prime hr).mp g3
              rcases g3 with g3 | g3
              -- q cannot be 1 since it's prime
              .
                have hq1:= Nat.Prime.one_lt hq
                linarith
              -- Case: q = 2
              .
                subst q
                ring_nf at h
                rw [←h] at h3
                -- Contradiction: p is even but we proved it's odd
                absurd h3
                decide
            -- Case: q = 2
            .
              subst q
              rw [←h] at g
              ring_nf at g
              rw [show r * a * 4 + r ^ 2 * a * 2 = r * (a * 4 + r * a * 2) by ring] at g
              rw [show 16 + r * 20 + r ^ 2 * 10 + r ^ 3 * 2 = 2 ^ 4 + r * (20 + r * (10 + r * 2)) by ring] at g
              have g1 : r ∣ r * (a * 4 + r * a * 2):= by simp
              rw [g] at g1
              have g2 : r ∣ r * (20 + r * (10 + r * 2)):= by simp
              -- r divides 2^4
              replace g1 : r ∣ 2 ^ 4:= by exact (Nat.dvd_add_iff_left g2).mpr g1
              -- r divides 2
              have g3 : r ∣ 2:= by exact Nat.Prime.dvd_of_dvd_pow hr g1
              replace g3 : r = 1 ∨ r = 2:= by exact (Nat.dvd_prime hq).mp g3
              rcases g3 with g3 | g3
              -- r cannot be 1 since it's prime
              .
                have hr1:= Nat.Prime.one_lt hr
                linarith
              -- Case: r = 2
              .
                subst r
                ring_nf at h
                rw [←h] at h3
                -- Contradiction: p is even but we proved it's odd
                absurd h3
                decide
          -- Case: neither r nor q is 2
          .
            simp at h5
            rcases h5 with ⟨h5, h6⟩
            -- Both r and q are odd
            replace h5 : Odd r:= by exact Nat.Prime.odd_of_ne_two hr h5
            replace h6 : Odd q:= by exact Nat.Prime.odd_of_ne_two hq h6
            -- r + q is even
            replace h5 : Even (r + q):= by exact Odd.add_odd h5 h6
            replace h5 : 2 ∣ r + q:= by exact even_iff_two_dvd.mp h5
            rw [h] at h5
            -- Contradiction: p is odd but r+q = p is even
            absurd h3
            simp
            exact (even_iff_exists_two_nsmul p).mpr h5
      -- Apply the helper lemma to each case
      rcases h1 with h1 | h1 | h1
      -- Case: p is the largest
      .
        specialize h2 p q r ⟨hp, hq, hr⟩ h1 h
        trivial
      -- Case: q is the largest
      .
        specialize h2 q r p ⟨hq, hr, hp⟩ h1 (by linarith only [h])
        trivial
      -- Case: r is the largest
      .
        specialize h2 r p q ⟨hr, hp, hq⟩ h1 (by linarith only [h])
        trivial
  -- Reverse direction: if a = 6, then such primes exist
  .
    intro h
    -- Use p = q = r = 2 as a solution
    use 2, 2, 2
    norm_num
    subst a
    simp
