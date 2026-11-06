import Mathlib
/- Suppose that $a, b, c,d$ are pairwise distinct positive integers such that $a+b = c+d = p$ for some odd prime $p > 3$ . Prove that $abcd$ is not a perfect square. -/
theorem number_theory_68056 (a b c d p : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (hp : Nat.Prime p) (hp1 : p > 3) (h1 : a + b = p) (h2 : c + d = p) (h3 : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) : ¬(IsSquare (a * b * c * d)):= by
  -- Proof by contradiction: assume a*b*c*d is a perfect square
  by_contra H
  -- Extract the square root m such that m^2 = a*b*c*d
  rcases H with ⟨m, hm⟩
  -- Show that p is odd (since p > 3 and p is prime)
  have hp2 : Odd p:= by exact Nat.Prime.odd_of_ne_two hp (by omega)
  -- Key lemma: for distinct positive integers a, b, we have 4*a*b < (a+b)^2
  have h4 : ∀ a b : ℕ, a ≠ b → 4 * a * b < (a + b) ^ 2:= by
    intro a b h
    zify
    -- Convert to integers and show (a-b)^2 > 0
    replace h : (a : ℤ) - b ≠ 0:= by
      by_contra H
      absurd h
      zify
      linarith
    suffices ((a : ℤ) - b) ^ 2 > 0 by linarith
    positivity
  -- Show that a*d ≠ b*c (crucial for the proof)
  have h5 : a * d ≠ b * c:= by
    by_contra H
    -- If a*d = b*c, then (a+b)*d = b*(c+d)
    replace H : (a + b) * d = b * (c + d):= by linarith
    rw [h1, h2] at H
    rw [show b * p = p * b by ring] at H
    -- This implies d = b, contradicting distinctness
    replace H : d = b:= by
      replace hp1 : p > 0:= by omega
      exact Nat.eq_of_mul_eq_mul_left hp1 H
    omega
  -- Show that a*c + b*d < p^2
  have h6 : a * c + b * d < p ^ 2:= by
    rw [show p ^ 2 = (a + b) * (c + d) by rw [h1, h2] ; ring]
    suffices a * d + b * c > 0 by linarith
    positivity
  -- Show that p does not divide a*c + b*d
  have h7 : ¬(p ∣ a * c + b * d):= by
    by_contra H
    -- If p divides a*c + b*d, then p divides 2*a*c
    replace H : p ∣ 2 * a * c:= by
      zify at H h1 h2 ⊢
      rw [show (b : ℤ) = p - a by linarith] at H
      rw [show (d : ℤ) = p - c by linarith] at H
      rw [show (a : ℤ) * c + (p - a) * (p - c) = 2 * a * c + p * (p - a - c) by ring] at H
      suffices (p : ℤ) ∣ (p : ℤ) * (p - a - c) by exact (Int.dvd_iff_dvd_of_dvd_add H).mpr this
      simp
    -- Since p is odd and coprime with 2, p must divide a*c
    replace hp2 : Nat.Coprime p 2:= by exact Nat.coprime_two_right.mpr hp2
    rw [show 2 * a * c = 2 * (a * c) by ring] at H
    replace H : p ∣ a * c:= by exact Nat.Coprime.dvd_of_dvd_mul_left hp2 H
    -- Since p is prime, p must divide a or c
    replace H : p ∣ a ∨ p ∣ c:= by exact (Nat.Prime.dvd_mul hp).mp H
    rcases H with H | H
    all_goals
      apply Nat.le_of_dvd (by omega) at H
      linarith
  -- Show that 4*m < p^2 using the key lemma
  replace h4 : 4 * m < p ^ 2:= by
    have g1:= h4 a b (by omega)
    have g2:= h4 c d (by omega)
    rw [h1] at g1
    rw [h2] at g2
    suffices (4 * m) ^ 2 < (p ^ 2) ^ 2 by exact lt_of_pow_lt_pow_left' 2 this
    rw [show (p ^ 2) ^ 2 = p ^ 2 * p ^ 2 by ring]
    rw [show (4 * m) ^ 2 = 4 * a * b * (4 * c * d) by linarith]
    exact Nat.mul_lt_mul_of_lt_of_lt g1 g2
  -- Lemma: if m^2 ≡ k^2 (mod p), then p divides m+k or m-k
  have h8 : ∀ k : ℕ, m ^ 2 ≡ k ^ 2 [ZMOD p] → p ∣ m + k ∨ (p : ℤ) ∣ (m : ℤ) - k:= by
    intro k hk
    replace hk : (p : ℤ) ∣ (m : ℤ) ^ 2 - k ^ 2:= by exact Int.ModEq.dvd (id (Int.ModEq.symm hk))
    rw [show (m : ℤ) ^ 2 - k ^ 2 = (m + k) * (m - k) by ring] at hk
    replace hp : Prime (p : ℤ):= by exact Nat.prime_iff_prime_int.mp hp
    replace hk : (p : ℤ) ∣ (m : ℤ) + k ∨ (p : ℤ) ∣ (m : ℤ) - k:= by exact Prime.dvd_or_dvd hp hk
    rcases hk with hk | hk
    .
      left
      zify
      exact hk
    .
      right
      exact hk
  -- Show that m^2 ≡ (a*c)^2 (mod p)
  have h9 : m ^ 2 ≡ (a * c) ^ 2 [ZMOD p]:= by
    -- Since a + b = p, we have b ≡ -a (mod p)
    replace h1 : b ≡ -a [ZMOD p]:= by
      suffices (p : ℤ) ∣ (-a) - (b : ℤ) by exact Int.modEq_iff_dvd.mpr this
      use -1
      zify at h1
      linarith only [h1]
    -- Since c + d = p, we have d ≡ -c (mod p)
    replace h2 : d ≡ -c [ZMOD p]:= by
      suffices (p : ℤ) ∣ (-c) - (d : ℤ) by exact Int.modEq_iff_dvd.mpr this
      use -1
      zify at h2
      linarith only [h2]
    -- Multiply the congruences
    replace h1:= Int.ModEq.mul h1 h2
    ring_nf at h1
    replace h3 : a * c ≡ a * c [ZMOD p]:= by rfl
    replace h1:= Int.ModEq.mul h1 h3
    ring_nf at hm
    zify at hm
    rw [show (b : ℤ) * d * (a * c) = m ^ 2 by rw [←hm] ; ring_nf] at h1
    rw [show (a : ℤ) * c * (a * c) = (a * c) ^ 2 by ring] at h1
    exact h1
  -- Show that m^2 ≡ (b*d)^2 (mod p)
  have h10 : m ^ 2 ≡ (b * d) ^ 2 [ZMOD p]:= by
    -- Since a + b = p, we have a ≡ -b (mod p)
    replace h1 : a ≡ -b [ZMOD p]:= by
      suffices (p : ℤ) ∣ (-b) - (a : ℤ) by exact Int.modEq_iff_dvd.mpr this
      use -1
      zify at h1
      linarith only [h1]
    -- Since c + d = p, we have c ≡ -d (mod p)
    replace h2 : c ≡ -d [ZMOD p]:= by
      suffices (p : ℤ) ∣ (-d) - (c : ℤ) by exact Int.modEq_iff_dvd.mpr this
      use -1
      zify at h2
      linarith only [h2]
    -- Multiply the congruences
    replace h1:= Int.ModEq.mul h1 h2
    ring_nf at h1
    replace h3 : b * d ≡ b * d [ZMOD p]:= by rfl
    replace h1:= Int.ModEq.mul h1 h3
    ring_nf at hm
    zify at hm
    rw [show (a : ℤ) * c * (b * d) = m ^ 2 by rw [←hm] ; ring_nf] at h1
    rw [show (b : ℤ) * d * (b * d) = (b * d) ^ 2 by ring] at h1
    exact h1
  -- Apply the lemma to both congruences
  replace h9:= h8 (a * c) (by simp ; exact h9)
  replace h10:= h8 (b * d) (by simp ; exact h10)
  simp at h9 h10
  -- Show that p and m are coprime
  replace h8 : Nat.Coprime p m:= by
    by_contra H
    replace H : p ∣ m:= by exact (Nat.Prime.dvd_iff_not_coprime hp).mpr H
    replace H : p ∣ m * m:= by exact Dvd.dvd.mul_right H m
    rw [←hm] at H
    replace H:= (Nat.Prime.dvd_mul hp).mp H
    rcases H with H | H
    .
      replace H:= (Nat.Prime.dvd_mul hp).mp H
      rcases H with H | H
      .
        replace H:= (Nat.Prime.dvd_mul hp).mp H
        rcases H with H | H
        all_goals
          apply Nat.le_of_dvd (by omega) at H
          linarith
      .
        apply Nat.le_of_dvd (by omega) at H
        linarith
    .
      apply Nat.le_of_dvd (by omega) at H
      linarith
  -- Case analysis based on the divisibility conditions
  rcases h9 with h9 | h9
  .
    rcases h10 with h10 | h10
    .
      -- Case 1: p divides both m + a*c and m + b*d
      replace h9 : p * p ∣ (m + a * c) * (m + b * d):= by exact Nat.mul_dvd_mul h9 h10
      rw [show (m + a * c) * (m + b * d) = m ^ 2 + a * b * c * d + m * (a * c + b * d) by ring] at h9
      rw [hm] at h9
      rw [show m ^ 2 + m * m + m * (a * c + b * d) = m * (2 * m + a * c + b * d) by ring] at h9
      rw [show p * p = p ^ 2 by ring] at h9
      -- Since p^2 and m are coprime, p^2 must divide 2*m + a*c + b*d
      replace h9 : p ^ 2 ∣ 2 * m + a * c + b * d:= by
        replace h8 : Nat.Coprime (p ^ 2) m:= by exact Nat.Coprime.pow_left 2 h8
        exact Nat.Coprime.dvd_of_dvd_mul_left h8 h9
      rcases h9 with ⟨k, hk⟩
      -- Show that k must be positive
      have hk1 : k > 0:= by
        by_contra H
        simp at H
        subst k
        simp at hk
        omega
      -- Show that k < 2
      have hk2 : k < 2:= by
        by_contra H
        simp at H
        replace H : p ^ 2 * k ≥ p ^ 2 * 2:= by exact Nat.mul_le_mul_left (p ^ 2) H
        linarith
      -- Therefore k = 1
      replace hk1 : k = 1:= by omega
      subst k
      simp at hk
      rw [show p ^ 2 = (a + b) * (c + d) by rw [h1, h2] ; ring] at hk
      replace hk : 2 * m = a * d + b * c:= by linarith
      -- This leads to a contradiction with h5
      replace hm : (2 * a * d) * (2 * b * c) = (a * d + b * c) ^ 2:= by rw [←hk] ; linarith
      zify at hm
      replace hm : ((a : ℤ) * d - b * c) ^ 2 = 0:= by linarith
      simp at hm
      absurd h5
      zify
      linarith
    .
      -- Case 2: p divides m + a*c but not m + b*d
      zify at h9
      replace h9:= Int.dvd_sub h9 h10
      ring_nf at h9
      absurd h7
      zify
      exact h9
  .
    rcases h10 with h10 | h10
    .
      -- Case 3: p divides m + b*d but not m + a*c
      zify at h10
      replace h9:= Int.dvd_sub h10 h9
      ring_nf at h9
      absurd h7
      zify
      rw [show (a : ℤ) * c + b * d = b * d + a * c by ring]
      exact h9
    .
      -- Case 4: p divides m - a*c and m - b*d
      replace h9:= Int.mul_dvd_mul h9 h10
      zify at hm
      rw [show ((m : ℤ) - a * c) * (m - b * d) = m * (2 * m - a * c - b * d) by linarith] at h9
      replace h8 : Nat.Coprime (p ^ 2) m:= by exact Nat.Coprime.pow_left 2 h8
      rw [show (p : ℤ) * p = p ^ 2 by ring] at h9
      replace h8 : IsCoprime ((p : ℤ) ^ 2) (m : ℤ):= by exact Int.isCoprime_iff_gcd_eq_one.mpr h8
      replace h9 : (p : ℤ) ^ 2 ∣ 2 * (m : ℤ) - a * c - b * d:= by exact IsCoprime.dvd_of_dvd_mul_left h8 h9
      rw [show 2 * (m : ℤ) - a * c - b * d = 2 * m - (a * c + b * d) by ring] at h9
      -- Case analysis on whether 2*m ≥ a*c + b*d
      by_cases g : 2 * m ≥ a * c + b * d
      .
        -- Subcase: 2*m ≥ a*c + b*d
        replace h9 : p ^ 2 ∣ 2 * m - (a * c + b * d):= by
          zify
          field_simp
          exact h9
        by_cases g1 : 2 * m = a * c + b * d
        .
          -- If 2*m = a*c + b*d, we get a contradiction
          replace g1 : (2 * m) ^ 2 = (a * c + b * d) ^ 2:= by rw [g1]
          replace g1 : 4 * a * b * c * d = (a * c + b * d) ^ 2:= by linarith
          zify at g1
          replace g1 : ((a : ℤ) * c - b * d) ^ 2 = 0:= by linarith
          simp at g1
          replace g1 : ((a : ℤ) + b) * c - b * (c + d) = 0:= by linarith
          zify at h1 h2
          rw [h1, h2] at g1
          rw [show (p : ℤ) * c - b * p = p * (c - b) by ring] at g1
          simp at g1
          rcases g1 with g1 | g1
          .
            zify at hp1
            subst p
            simp at hp1
          .
            replace g1 : c = b:= by
              zify
              linarith only [g1]
            omega
        .
          -- Otherwise, we get a contradiction with the bounds
          apply Nat.le_of_dvd (by omega) at h9
          omega
      .
        -- Subcase: 2*m < a*c + b*d
        simp at g
        replace h9 : (p : ℤ) ^ 2 ∣ (-1) * (2 * (m : ℤ) - (a * c + b * d)):= by exact Dvd.dvd.mul_left h9 (-1)
        rw [show -1 * (2 * (↑m : ℤ) - (↑a * ↑c + ↑b * ↑d)) = a * c + b * d - 2 * ↑m by ring] at h9
        replace g9 : p ^ 2 ∣ a * c + b * d - 2 * m:= by
          zify
          have g1 : a * c + b * d ≥ 2 * m:= by omega
          field_simp
          exact h9
        apply Nat.le_of_dvd (by omega) at g9
        omega
