import Mathlib
/- Let $a,b,c$ be positive integers greater than $1$ such that $$p=ab+bc+ac$$ is prime.
A) Prove that $a^2, b^2, c^2$ all have different reminder $mod\  p$.
B) Prove that $a^3, b^3, c^3$ all have different reminder $mod\  p$. -/
theorem algebra_33612 (a b c p : ℕ) (ha : a > 1) (hb : b > 1) (hc : c > 1) (hp : Nat.Prime p) (h : p = a * b + b * c + c * a) : (¬(a ^ 2 ≡ b ^ 2 [MOD p]) ∧ ¬(b ^ 2 ≡ c ^ 2 [MOD p]) ∧ ¬(c ^ 2 ≡ a ^ 2 [MOD p])) ∧ (¬(a ^ 3 ≡ b ^ 3 [MOD p]) ∧ ¬(b ^ 3 ≡ c ^ 3 [MOD p]) ∧ ¬(c ^ 3 ≡ a ^ 3 [MOD p])):= by
  -- Helper lemma: For any three positive integers a,b,c > 1 with p = ab + bc + ac,
  -- prove that a² ≢ b² (mod p) and a³ ≢ b³ (mod p)
  have h1 : ∀ a b c : ℕ, a > 1 → b > 1 → c > 1 → p = a * b + b * c + c * a → ¬(a ^ 2 ≡ b ^ 2 [MOD p]) ∧ ¬(a ^ 3 ≡ b ^ 3 [MOD p]):= by
    intro a b c ha hb hc h
    -- First, prove that p > a + b + c
    have h1 : p > a + b + c:= by
      rw [h]
      -- Show that each product term is greater than its individual factor
      have g1 : a * b > a:= by refine (Nat.lt_mul_iff_one_lt_right (by omega)).mpr hb
      have g2 : b * c > b:= by refine (Nat.lt_mul_iff_one_lt_right (by omega)).mpr hc
      have g3 : c * a > c:= by refine (Nat.lt_mul_iff_one_lt_right (by omega)).mpr ha
      linarith
    -- Prove that a ≠ b by contradiction
    have h2 : a ≠ b:= by
      by_contra H
      subst a
      replace h : b * (2 * c + b) = p:= by linarith
      replace h : b ∣ p:= by
        use 2 * c + b
        linarith
      replace h : b = 1 ∨ b = p:= by exact (Nat.dvd_prime hp).mp h
      rcases h with h | h
      all_goals
        linarith
    -- Prove that b ≠ c by contradiction
    have h3 : b ≠ c:= by
      by_contra H
      subst b
      replace h : c * (2 * a + c) = p:= by linarith
      replace h : c ∣ p:= by
        use 2 * a + c
        linarith
      replace h : c = 1 ∨ c = p:= by exact (Nat.dvd_prime hp).mp h
      rcases h with h | h
      all_goals
        linarith
    -- Prove that c ≠ a by contradiction
    have h4 : c ≠ a:= by
      by_contra H
      subst c
      replace h : a * (2 * b + a) = p:= by linarith
      replace h : a ∣ p:= by
        use 2 * b + a
        linarith
      replace h : a = 1 ∨ a = p:= by exact (Nat.dvd_prime hp).mp h
      rcases h with h | h
      all_goals
        linarith
    refine ⟨?_, ?_⟩
    .
      -- Prove a² ≢ b² (mod p) by contradiction
      by_contra H
      -- Lemma: If a > b and a² ≡ b² (mod p), then p ≤ a + b
      have g1 : ∀ a b : ℕ, a > 1 → b > 1 → a > b → a ^ 2 ≡ b ^ 2 [MOD p] → p ≤ a + b:= by
        intro a b ha hb h g
        have hab : a ≥ b:= by omega
        have gab : a ^ 2 ≥ b ^ 2:= by exact Nat.pow_le_pow_of_le_left hab 2
        replace g : p ∣ a ^ 2 - b ^ 2:= by exact (Nat.modEq_iff_dvd' gab).mp (id (Nat.ModEq.symm g))
        -- Factor a² - b² = (a - b)(a + b)
        have g1 : a ^ 2 - b ^ 2 = (a - b) * (a + b):= by
          zify
          field_simp
          ring
        rw [g1] at g
        replace g : p ∣ a - b ∨ p ∣ a + b:= by exact (Nat.Prime.dvd_mul hp).mp g
        rcases g with g | g
        all_goals
          apply Nat.le_of_dvd (by omega) at g
          omega
      replace h2 : a < b ∨ a > b:= by omega
      rcases h2 with h2 | h2
      .
        -- Case: a < b
        replace g1:= g1 b a hb ha h2 (by exact id (Nat.ModEq.symm H))
        linarith
      .
        -- Case: a > b
        replace g1:= g1 a b ha hb h2 H
        linarith
    -- Prove a³ ≢ b³ (mod p) by contradiction
    have g2 : ∀ a b : ℕ, a > 1 → b > 1 → a > b → a ≠ c → p = a * b + b * c + c * a → a ^ 3 ≡ b ^ 3 [MOD p] → p ≤ a + b + c:= by
      intro a b ha hb h hac h1 g
      have hab : a ≥ b:= by omega
      have gab : a ^ 3 ≥ b ^ 3:= by exact Nat.pow_le_pow_of_le_left hab 3
      replace g : p ∣ a ^ 3 - b ^ 3:= by exact (Nat.modEq_iff_dvd' gab).mp (id (Nat.ModEq.symm g))
      -- Factor a³ - b³ = (a - b)(a² + ab + b²)
      have g1 : a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2):= by
        zify
        field_simp
        ring
      rw [g1] at g
      replace g:= (Nat.Prime.dvd_mul hp).mp g
      rcases g with g | g
      .
        -- Case: p ∣ a - b
        apply Nat.le_of_dvd (by omega) at g
        omega
      .
        -- Case: p ∣ a² + ab + b²
        have g0:= g
        rw [show a * b + b * c + c * a = a * (b + c) + b * c by linarith] at h1
        replace g : p ∣ (a ^ 2 + a * b + b ^ 2) * (b + c) ^ 2:= by exact Dvd.dvd.mul_right g ((b + c) ^ 2)
        rw [show (a ^ 2 + a * b + b ^ 2) * (b + c) ^ 2 = (a * (b + c)) ^ 2 + a * (b + c) * ((b * (b + c))) + b ^ 2 * (b + c) ^ 2 by linarith] at g
        zify at g h1
        rw [show (a : ℤ) * (b + c) = p - b * c by linarith] at g
        rw [show ((↑p : ℤ) - ↑b * ↑c) ^ 2 + (↑p - ↑b * ↑c) * (↑b * (↑b + ↑c)) + ↑b ^ 2 * (↑b + ↑c) ^ 2 = p * (p - 2 * b * c + b * (b + c)) + b ^ 2 * (b ^ 2 + b * c + c ^ 2) by ring] at g
        have g2 : (p : ℤ) ∣ (↑p : ℤ) * (↑p - 2 * ↑b * ↑c + ↑b * (↑b + ↑c)):= by simp
        replace g : p ∣ b ^ 2 * (b ^ 2 + b * c + c ^ 2):= by
          zify
          exact (Int.dvd_iff_dvd_of_dvd_add g).mp g2
        replace g:= (Nat.Prime.dvd_mul hp).mp g
        rcases g with g | g
        .
          -- Case: p ∣ b²
          replace g : p ∣ b:= by exact Nat.Prime.dvd_of_dvd_pow hp g
          apply Nat.le_of_dvd (by omega) at g
          linarith
        .
          -- Case: p ∣ b² + bc + c²
          replace g : (p : ℤ) ∣ ((a : ℤ) - c) * (a + b + c):= by
            rw [show ((a : ℤ) - c) * (a + b + c) = a ^ 2 + a * b + b ^ 2 + -1 * (b ^ 2 + b * c + c ^ 2) by linarith]
            zify at g g0
            replace g : (p : ℤ) ∣ -1 * ((b : ℤ) ^ 2 + b * c + c ^ 2):= by exact Dvd.dvd.mul_left g (-1)
            exact (Int.dvd_add_right g0).mpr g
          replace hac : a < c ∨ a > c:= by omega
          rcases hac with hac | hac
          .
            -- Case: a < c
            have gac : c ≥ a:= by omega
            replace g : p ∣ (c - a) * (a + b + c):= by
              zify
              field_simp
              rcases g with ⟨k, hk⟩
              use -k
              linarith
            replace g:= (Nat.Prime.dvd_mul hp).mp g
            rcases g with g | g
            all_goals
              apply Nat.le_of_dvd (by omega) at g
              omega
          .
            -- Case: a > c
            have gac : a ≥ c:= by omega
            replace g : p ∣ (a - c) * (a + b + c):= by
              zify
              field_simp
              exact g
            replace g:= (Nat.Prime.dvd_mul hp).mp g
            rcases g with g | g
            all_goals
              apply Nat.le_of_dvd (by omega) at g
              omega
    by_contra H
    replace h2 : a < b ∨ a > b:= by omega
    rcases h2 with h2 | h2
    .
      -- Case: a < b
      replace g2:= g2 b a hb ha h2 h3 (by linarith) (by exact id (Nat.ModEq.symm H))
      linarith
    .
      -- Case: a > b
      replace g2:= g2 a b ha hb h2 (by omega) h H
      linarith
  -- Apply the helper lemma to all three pairs of variables
  have g1:= h1 a b c ha hb hc h
  have g2:= h1 b c a hb hc ha (by linarith)
  have g3:= h1 c a b hc ha hb (by linarith)
  -- Combine all results to prove the main theorem
  exact ⟨⟨g1.1, g2.1, g3.1⟩, ⟨g1.2, g2.2, g3.2⟩⟩
