import Mathlib
/- Let $n>1$ be a positive integer and $p$ a prime number such that $n \mid(p-1)$ and $p \mid\left(n^{6}-1\right)$. Prove that at least one of the numbers $p-n$ and $p+n$ is a perfect square. -/
theorem algebra_604596 (n p : ℕ) (hn : n > 1) (hp : Nat.Prime p) (h1 : n ∣ p - 1) (h2 : p ∣ n ^ 6 - 1) : (∃ k : ℕ, p - n = k ^ 2) ∨ (∃ k : ℕ, p + n = k ^ 2):= by
  -- From n divides (p-1), we get that p-1 = n*a for some natural number a
  have h3 : ∃ a : ℕ, p - 1 = n * a:= by exact h1
  rcases h3 with ⟨a, ha⟩
  -- Since p is prime, p > 1
  have hp1 : p > 1:= by exact Nat.Prime.one_lt hp
  -- Rewrite p = n*a + 1
  replace ha : p = n * a + 1:= by omega

  -- Factor n^6 - 1 into (n-1)(n+1)(n^2+n+1)(n^2-n+1)
  have h3 : n ^ 6 - 1 = (n - 1) * (n + 1) * (n ^ 2 + n + 1) * (n ^ 2 - n + 1):= by
    suffices n ^ 6 = (n - 1) * (n + 1) * (n ^ 2 + n + 1) * (n ^ 2 - n + 1) + 1 by omega
    -- Algebraic manipulation to prove the factorization
    have g1 : n ^ 2 = n * (n - 1) + n:= by
      zify
      have g2 : n - 1 + 1 = n:= by omega
      zify at g2
      replace g2 : (↑(n - 1) : ℤ) = (↑n : ℤ) - 1:= by linarith
      rw [g2]
      ring_nf
    replace g1 : n ^ 2 - n = n * (n - 1):= by omega
    rw [g1]
    set m:= n - 1
    replace hn : m > 0:= by omega
    replace hm : n = m + 1:= by omega
    clear_value m
    subst n
    ring_nf

  -- Since p divides n^6-1, p must divide one of the factors
  rw [h3] at h2
  replace h2 : p ∣ (n - 1) * (n + 1) * (n ^ 2 + n + 1) ∨ p ∣ (n ^ 2 - n + 1):= by exact (Nat.Prime.dvd_mul hp).mp h2
  simp [Nat.Prime.dvd_mul hp] at h2
  -- Consider all possible cases of which factor p divides
  rcases h2 with ⟨⟨h2 | h2⟩ | h2⟩ | h2

  -- Case 1: p divides (n-1)
  .
    replace h2 : ∃ t : ℕ, n - 1 = p * t:= by exact h2
    rcases h2 with ⟨t, ht⟩
    -- Prove t ≥ 1
    have htpos : t ≥ 1:= by
      by_contra H
      simp at H
      subst t
      simp at ht
      omega
    replace htpos : p * t ≥ p:= by exact Nat.le_mul_of_pos_right p htpos
    rw [←ht] at htpos
    -- Prove a ≥ 1
    have hapos : a ≥ 1:= by
      by_contra H
      simp at H
      subst a
      simp at ha
      omega
    replace hapos : n * a ≥ n:= by exact Nat.le_mul_of_pos_right n hapos
    by_contra _
    omega

  -- Case 2: p divides (n+1)
  .
    replace h2 : ∃ t : ℕ, n + 1 = p * t:= by exact h2
    rcases h2 with ⟨t, ht⟩
    -- Prove t ≥ 1
    have htpos : t ≥ 1:= by
      by_contra H
      simp at H
      subst t
      simp at ht
    have ht1 : p * t ≥ p:= by exact Nat.le_mul_of_pos_right p htpos
    -- Prove a ≥ 1
    have hapos : a ≥ 1:= by
      by_contra H
      simp at H
      subst a
      simp at ha
      omega
    have ha1 : n * a ≥ n:= by exact Nat.le_mul_of_pos_right n hapos
    -- Prove p-n = 1^2, so p-n is a perfect square
    left
    use 1
    simp
    omega

  -- Case 3: p divides (n^2+n+1)
  .
    replace h2 : ∃ b : ℕ, n ^ 2 + n + 1 = p * b:= by exact h2
    rcases h2 with ⟨b, hb⟩
    -- Prove b ≥ 1
    have hbpos : b ≥ 1:= by
      by_contra H
      simp at H
      subst b
      simp at hb
    clear h3
    -- Prove n divides (b-1)
    have h3 : n ∣ b - 1:= by
      rw [ha] at hb
      ring_nf at hb
      replace hb : n * (n + 1) = n * (a * b) + (b - 1):= by ring_nf ; omega
      replace hb : n ∣ (n * (a * b) + (b - 1)):= by exact Dvd.intro (n + 1) hb
      have g1 : n ∣ n * (a * b):= by exact Nat.dvd_mul_right n (a * b)
      exact (Nat.dvd_add_iff_right g1).mpr hb
    replace h3 : ∃ c : ℕ, b - 1 = n * c:= by exact h3
    rcases h3 with ⟨c, hc⟩
    replace hc : b = n * c + 1:= by omega
    -- Derive a relationship between n, a, and c
    have h3 : n + 1 = a * c * n + a + c:= by
      rw [ha, hc] at hb
      ring_nf at hb
      replace hb : n * (n + 1) = n * (a * c * n + a + c):= by ring_nf ; omega
      rify
      rify at hb
      replace hb : n * (n + (1 : ℝ) - (a * c * n + a + c)) = 0:= by linarith
      replace hn : n ≠ 0:= by omega
      simp [hn] at hb
      linarith
    -- Consider two cases: a*c ≥ 1 or a*c = 0
    by_cases hac : a * c ≥ 1
    .
      by_contra _
      have g1 : a * c * n ≥ n:= by exact Nat.le_mul_of_pos_left n hac
      have ha1 : a ≥ 1:= by
        by_contra H
        simp at H
        subst a
        simp at hac
      have hc1 : c ≥ 1:= by
        by_contra H
        simp at H
        subst c
        simp at hac
      linarith
    .
      simp at hac
      rcases hac with hac | hac
      .
        by_contra _
        subst a
        simp at ha
        linarith
      .
        subst c
        simp at hc
        subst b
        simp at hb
        -- Prove p+n = (n+1)^2, so p+n is a perfect square
        right
        use (n + 1)
        linarith

  -- Case 4: p divides (n^2-n+1)
  .
    replace h2 : ∃ b : ℕ, n ^ 2 - n + 1 = p * b:= by exact h2
    rcases h2 with ⟨b, hb⟩
    -- Prove b ≥ 1
    have hbpos : b ≥ 1:= by
      by_contra H
      simp at H
      subst b
      simp at hb
    -- Algebraic manipulation
    have g1 : n ^ 2 = n * (n - 1) + n:= by
      zify
      have g2 : n - 1 + 1 = n:= by omega
      zify at g2
      replace g2 : (↑(n - 1) : ℤ) = (↑n : ℤ) - 1:= by linarith
      rw [g2]
      ring_nf
    replace g1 : n ^ 2 - n = n * (n - 1):= by omega
    -- Prove n divides (b-1)
    have h3 : n ∣ b - 1:= by
      rw [ha] at hb
      ring_nf at hb
      rw [g1] at hb
      replace hb : n * (n - 1) = n * (a * b) + (b - 1):= by ring_nf ; omega
      replace hb : n ∣ (n * (a * b) + (b - 1)):= by exact Dvd.intro (n - 1) hb
      have g1 : n ∣ n * (a * b):= by exact Nat.dvd_mul_right n (a * b)
      exact (Nat.dvd_add_iff_right g1).mpr hb
    replace h3 : ∃ c : ℕ, b - 1 = n * c:= by exact h3
    rcases h3 with ⟨c, hc⟩
    replace hc : b = n * c + 1:= by omega
    -- Derive a relationship between n, a, and c
    have h3 : n - 1 = a * c * n + a + c:= by
      rw [ha, hc] at hb
      ring_nf at hb
      replace hb : n * (n - 1) = n * (a * c * n + a + c):= by ring_nf ; omega
      rify
      rify at hb
      replace hb : n * ((↑(n - 1) : ℝ) - (a * c * n + a + c)) = 0:= by linarith
      replace hn : n ≠ 0:= by omega
      simp [hn] at hb
      linarith
    -- Consider two cases: a*c ≥ 1 or a*c = 0
    by_cases hac : a * c ≥ 1
    .
      by_contra _
      have g1 : a * c * n ≥ n:= by exact Nat.le_mul_of_pos_left n hac
      omega
    .
      simp at hac
      rcases hac with hac | hac
      .
        by_contra _
        subst a
        simp at ha
        linarith
      .
        subst c
        simp at hc
        subst b
        simp at hb
        -- Prove p-n = (n-1)^2, so p-n is a perfect square
        left
        use (n - 1)
        rw [g1] at hb
        set m:= n - 1 with hm
        clear_value m
        replace hm : n = m + 1:= by omega
        suffices p = m ^ 2 + n by omega
        subst n
        ring_nf
        ring_nf at hb
        rw [hb]
