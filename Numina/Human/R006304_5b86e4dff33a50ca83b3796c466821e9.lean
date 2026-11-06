import Mathlib
/- Let $M$ be a positive integer and $p$ be a prime number. Find all positive integers $a$ and $b$ such that the expressions $\frac{Ma+p}{b}+\frac{Mb+p}{a}$ and $\frac{a^2}{b}+\frac{b^2}{a}$ are both integers. Show the answer is that $a$ and $b$ must be equal, and $a$ must be a divisor of $2p$. -/
theorem number_theory_635686 (m p a b : ℕ) (hm : m > 0) (hp : Nat.Prime p) (ha : a > 0) (hb : b > 0) : (∃ n : ℕ, (m * a + p) / (b : ℝ) + (m * b + p) / a = n) ∧ (∃ n : ℕ, a ^ 2 / (b : ℝ) + b ^ 2 / a = n) ↔ (a = b ∧ a ∣ 2 * p ∨ ∃ c : ℕ, (c ∣ 1 + p ∧ p ∣ 1 + c * m) ∧ (a = p * c ∧ b = p ^ 2 * c ∨ a = p ^ 2 * c ∧ b = p * c)):= by
  constructor
  .
    -- First prove that p > 1 since p is prime
    have hppos : p > 1:= by exact Nat.Prime.one_lt hp
    intro ⟨h1, h2⟩
    -- Transform the first fraction equation into a divisibility condition
    replace h1 : a * b ∣ (a + b) * p + (a ^ 2 + b ^ 2) * m:= by
      rcases h1 with ⟨n, hn⟩
      field_simp at hn
      use n
      rify
      linarith
    -- Transform the second fraction equation into a divisibility condition
    replace h2 : a * b ∣ a ^ 3 + b ^ 3:= by
      rcases h2 with ⟨n, hn⟩
      field_simp at hn
      use n
      rify
      linarith
    -- Let d be the greatest common divisor of a and b
    set d:= Nat.gcd a b with hd
    clear_value d
    -- Show that d divides both a and b
    have g1 : d ∣ a:= by
      subst d
      exact Nat.gcd_dvd_left a b
    have g2 : d ∣ b:= by
      subst d
      exact Nat.gcd_dvd_right a b
    rcases g1 with ⟨a, rfl⟩
    rcases g2 with ⟨b, rfl⟩
    -- Use properties of GCD to simplify expressions
    rw [show Nat.gcd (d * a) (d * b) = d * Nat.gcd a b by exact Nat.gcd_mul_left d a b] at hd
    have hdpos : d > 0:= by
      exact Nat.pos_of_mul_pos_right ha
    replace ha : a > 0:= by exact Nat.pos_of_mul_pos_left ha
    replace hb : b > 0:= by exact Nat.pos_of_mul_pos_left hb
    replace hd : Nat.gcd a b = 1:= by exact (Nat.mul_right_eq_self_iff hdpos).mp (id (Eq.symm hd))
    -- Simplify expressions using algebraic manipulation
    rw [show (d * a) ^ 3 + (d * b) ^ 3 = d ^ 2 * (d * (a ^ 3 + b ^ 3)) by ring] at h2
    rw [show d * a * (d * b) = d ^ 2 * (a * b) by ring] at h2
    replace h2 : a * b ∣ d * (a ^ 3 + b ^ 3):= by exact (mul_dvd_mul_iff_left (by positivity)).mp h2
    -- Show that a divides d
    have h3 : a ∣ d:= by
      have h3 : a ∣ d * (a ^ 3 + b ^ 3):= by exact dvd_of_mul_right_dvd h2
      rw [show d * (a ^ 3 + b ^ 3) = d * b ^ 3 + a * (d * a ^ 2) by ring] at h3
      replace h3 : a ∣ d * b ^ 3:= by
        have h4 : a ∣ a * (d * a ^ 2):= by simp
        exact (Nat.dvd_add_iff_left h4).mpr h3
      replace hd : Nat.Coprime a (b ^ 3):= by exact Nat.Coprime.pow_right 3 hd
      exact Nat.Coprime.dvd_of_dvd_mul_right hd h3
    -- Show that b divides d
    have h4 : b ∣ d:= by
      have h4 : b ∣ d * (a ^ 3 + b ^ 3):= by exact dvd_of_mul_left_dvd h2
      rw [show d * (a ^ 3 + b ^ 3) = d * a ^ 3 + b * (d * b ^ 2) by ring] at h4
      replace h4 : b ∣ d * a ^ 3:= by
        have h5 : b ∣ b * (d * b ^ 2):= by simp
        exact (Nat.dvd_add_iff_left h5).mpr h4
      replace hd : Nat.gcd b a = 1:= by exact Nat.coprime_comm.mp hd
      replace hd : Nat.Coprime b (a ^ 3):= by exact Nat.Coprime.pow_right 3 hd
      exact Nat.Coprime.dvd_of_dvd_mul_right hd h4
    -- Show that a * b divides d
    replace h2 : a * b ∣ d:= by exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hd h3 h4
    clear h3 h4
    rcases h2 with ⟨c, rfl⟩
    -- Use the first divisibility condition to derive more properties
    ring_nf at h1
    rw [show a ^ 3 * b ^ 3 * c ^ 2 = (a * b * c) * (a ^ 2 * b ^ 2 * c) by ring] at h1
    rw [show a * b ^ 2 * c * p + a ^ 2 * b * c * p + a ^ 2 * b ^ 4 * c ^ 2 * m + a ^ 4 * b ^ 2 * c ^ 2 * m = a * b * c * ((a + b) * p + a * b * c * m * (a ^ 2 + b ^ 2)) by ring_nf] at h1
    replace h1 : (a ^ 2 * b ^ 2 * c) ∣ ((a + b) * p + a * b * c * m * (a ^ 2 + b ^ 2)):= by exact (mul_dvd_mul_iff_left (by positivity)).mp h1
    -- Show that a divides p
    have h2 : a ∣ p:= by
      have h2 : a ∣ a ^ 2 * b ^ 2 * c:= by
        use a * b ^ 2 * c
        ring
      replace h2 : a ∣ (a + b) * p + a * b * c * m * (a ^ 2 + b ^ 2):= by exact Nat.dvd_trans h2 h1
      rw [show (a + b) * p + a * b * c * m * (a ^ 2 + b ^ 2) = b * p + a * (p + b * c * m * (a ^ 2 + b ^ 2)) by ring_nf] at h2
      replace h2 : a ∣ b * p:= by
        have h3 : a ∣ a * (p + b * c * m * (a ^ 2 + b ^ 2)):= by simp
        exact (Nat.dvd_add_iff_left h3).mpr h2
      exact Nat.Coprime.dvd_of_dvd_mul_left hd h2
    -- Show that b divides p
    have h3 : b ∣ p:= by
      have h3 : b ∣ a ^ 2 * b ^ 2 * c:= by
        use a ^ 2 * b * c
        ring
      replace h2:= Nat.dvd_trans h3 h1
      rw [show (a + b) * p + a * b * c * m * (a ^ 2 + b ^ 2) = a * p + b * (p + a * c * m * (a ^ 2 + b ^ 2)) by ring_nf] at h2
      replace h2 : b ∣ a * p:= by
        have h3 : b ∣ b * (p + a * c * m * (a ^ 2 + b ^ 2)):= by simp
        exact (Nat.dvd_add_iff_left h3).mpr h2
      replace hd : Nat.gcd b a = 1:= by exact Nat.coprime_comm.mp hd
      exact Nat.Coprime.dvd_of_dvd_mul_left hd h2
    -- Since p is prime, a and b must be either 1 or p
    replace h2 : a = 1 ∨ a = p:= by exact (Nat.dvd_prime hp).mp h2
    replace h3 : b = 1 ∨ b = p:= by exact (Nat.dvd_prime hp).mp h3
    -- Case analysis on the values of a and b
    rcases h2 with h2 | h2
    .
      rcases h3 with h3 | h3
      .
        subst a b
        simp at h1
        have h2 : c ∣ c * m * 2:= by
          use m * 2
          ring
        replace h1 : c ∣ 2 * p:= by exact (Nat.dvd_add_iff_left h2).mpr h1
        simp
        left
        exact h1
      .
        subst a b
        simp at h1
        rw [show (1 + p) * p + p * c * m * (1 + p ^ 2) = p * (1 + p + c * m * (1 + p ^ 2)) by ring] at h1
        rw [show p ^ 2 * c = p * (p * c) by ring] at h1
        replace h1 : p * c ∣ 1 + p + c * m * (1 + p ^ 2):= by exact Nat.dvd_of_mul_dvd_mul_left hb h1
        have h2 : c ∣ 1 + p:= by
          replace h1 : c ∣ 1 + p + c * m * (1 + p ^ 2):= by exact dvd_of_mul_left_dvd h1
          have h2 : c ∣ c * m * (1 + p ^ 2):= by
            use m * (1 + p ^ 2)
            ring
          exact (Nat.dvd_add_iff_left h2).mpr h1
        have h3 : p ∣ 1 + c * m:= by
          replace h1 : p ∣ 1 + p + c * m * (1 + p ^ 2):= by exact dvd_of_mul_right_dvd h1
          have h3 : p ∣ p * (1 + c * m * p):= by simp
          rw [show 1 + p + c * m * (1 + p ^ 2) = 1 + c * m + p * (1 + c * m * p) by ring] at h1
          exact (Nat.dvd_add_iff_left h3).mpr h1
        right
        use c
        refine ⟨⟨h2, h3⟩, ?_⟩
        ring_nf
        simp
    .
      rcases h3 with h3 | h3
      .
        subst a b
        simp at h1
        rw [show (p + 1) * p + p * c * m * (p ^ 2 + 1) = p * (1 + p + c * m * (1 + p ^ 2)) by ring] at h1
        rw [show p ^ 2 * c = p * (p * c) by ring] at h1
        replace h1 : p * c ∣ 1 + p + c * m * (1 + p ^ 2):= by exact Nat.dvd_of_mul_dvd_mul_left ha h1
        have h2 : c ∣ 1 + p:= by
          replace h1 : c ∣ 1 + p + c * m * (1 + p ^ 2):= by exact dvd_of_mul_left_dvd h1
          have h2 : c ∣ c * m * (1 + p ^ 2):= by
            use m * (1 + p ^ 2)
            ring
          exact (Nat.dvd_add_iff_left h2).mpr h1
        have h3 : p ∣ 1 + c * m:= by
          replace h1 : p ∣ 1 + p + c * m * (1 + p ^ 2):= by exact dvd_of_mul_right_dvd h1
          have h3 : p ∣ p * (1 + c * m * p):= by simp
          rw [show 1 + p + c * m * (1 + p ^ 2) = 1 + c * m + p * (1 + c * m * p) by ring] at h1
          exact (Nat.dvd_add_iff_left h3).mpr h1
        right
        use c
        refine ⟨⟨h2, h3⟩, ?_⟩
        ring_nf
        simp
      .
        subst a b
        rw [show Nat.gcd p p = p by exact Nat.gcd_self p] at hd
        linarith
  .
    -- Prove the reverse direction
    intro h
    rcases h with h | h
    .
      -- Case: a = b and a divides 2p
      rcases h with ⟨h1, h2⟩
      subst a
      rcases h2 with ⟨k, hk⟩
      constructor
      .
        -- Show that the first fraction is an integer
        use (2 * m + k)
        field_simp
        rify at hk
        linarith
      .
        -- Show that the second fraction is an integer
        use 2 * b
        field_simp
        ring
    .
      -- Case: a and b are related to p and c
      rcases h with ⟨c, ⟨h1, h2⟩⟩
      rcases h1 with ⟨g1, g2⟩
      have hppos : p > 1:= by exact Nat.Prime.one_lt hp
      rcases h2 with h2 | h2
      all_goals
        rcases h2 with ⟨h1, h2⟩
        subst a b
        constructor
        .
          -- Show that c is positive
          replace ha : c > 0:= by exact Nat.pos_of_mul_pos_left ha
          field_simp
          ring_nf
          -- Analyze the GCD of p and c
          have g3 : Nat.gcd p c ∣ p:= by exact Nat.gcd_dvd_left p c
          replace g3 : Nat.gcd p c = 1 ∨ Nat.gcd p c = p:= by exact (Nat.dvd_prime hp).mp g3
          rcases g3 with g3 | g3
          .
            -- Case: p and c are coprime
            replace g1 : c ∣ 1 + p + c * m:= by
              have g : c ∣ c * m:= by simp
              exact (Nat.dvd_add_iff_right g1).mp g
            replace g2 : p ∣ 1 + p + c * m:= by
              rcases g2 with ⟨k, hk⟩
              use k + 1
              linarith
            -- Show that p*c divides 1 + p + c*m
            replace g1 : p * c ∣ 1 + p + c * m:= by exact Nat.Coprime.mul_dvd_of_dvd_of_dvd g3 g2 g1
            rcases g1 with ⟨k, hk⟩
            use (m * p + k)
            rify at hk
            simp
            -- Complete the proof using algebraic manipulation
            suffices (p : ℝ) ^ 2 * c * (m * p ^ 2 * c + (1 + p + c * m) - p * c * m * p - p * c * k) = 0 by linarith
            rw [←hk]
            ring_nf
          .
            -- Case: p divides c
            replace g3 : p ∣ c:= by rw [←g3] ; exact Nat.gcd_dvd_right p c
            replace g1 : p ∣ 1 + p:= by exact Nat.dvd_trans g3 g1
            replace g1 : p ∣ 1:= by exact Nat.dvd_add_self_right.mp g1
            simp at g1
            linarith
        .
          -- Show that the second fraction is an integer
          replace ha : c > 0:= by exact Nat.pos_of_mul_pos_left ha
          use (c + p ^ 3 * c)
          field_simp
          ring_nf
