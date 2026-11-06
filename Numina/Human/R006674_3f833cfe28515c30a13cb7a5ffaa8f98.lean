import Mathlib
/- Let $M$ be a positive integer. Determine the $M$-th digit from the rightmost end of the number $N = 5^{5^{5^{5^{5}}}}$. Show that for $M=4$, the answer is $3$. -/
theorem algebra_639939 (n m : ℕ) (hm : m = 5) (hn : n = 5 ^ 5 ^ 5 ^ m ^ m) : (n / 1000) ≡ 3 [MOD 10]:= by
  have h1 : (n / 1000) % 10 = ((n % 10000) / 1000) % 10:= by
    -- Express n as n = 10000 * q + r where r = n % 10000
    have g : n = 10000 * (n / 10000) + (n % 10000):= by omega
    set r:= n % 10000
    set q:= n / 10000
    clear_value r q
    rw [g]
    -- Rewrite 10000 * q as 1000 * (10 * q)
    rw [show 10000 * q = 1000 * (10 * q) by omega]
    -- Distribute division: (1000 * (10 * q) + r) / 1000 = 10 * q + r / 1000
    rw [show (1000 * (10 * q) + r) / 1000 = 10 * q + r / 1000 by omega]
    -- Show that 10 * q + r / 1000 ≡ r / 1000 [MOD 10]
    have g1 : 10 * q + r / 1000 ≡ r / 1000 [MOD 10]:= by
      -- 10 * q ≡ 0 [MOD 10] since 10 divides 10 * q
      have g1 : 10 * q ≡ 0 [MOD 10]:= by
        suffices 10 ∣ 10 * q by exact Nat.modEq_zero_iff_dvd.mpr this
        simp
      -- Add r / 1000 to both sides: 10 * q + r / 1000 ≡ 0 + r / 1000 [MOD 10]
      replace g1 : 10 * q + r / 1000 ≡ 0 + r / 1000 [MOD 10]:= by exact Nat.ModEq.add_right (r / 1000) g1
      simp at g1
      exact g1
    rw [g1]
  -- Lemma: 5^(4k) ≡ 1 [MOD 16] for all k
  have h2 : ∀ k : ℕ, 5 ^ (4 * k) ≡ 1 [MOD 16]:= by
    intro k
    induction k with
    | zero =>
      -- Base case: 5^0 = 1 ≡ 1 [MOD 16]
      simp
      rfl
    | succ k ih =>
      -- Inductive step: 5^(4(k+1)) = 5^(4k) * 5^4 ≡ 1 * 625 ≡ 1 [MOD 16]
      rw [show 4 * (k + 1) = 4 * k + 4 by omega]
      rw [show 5 ^ (4 * k + 4) = 5 ^ (4 * k) * 5 ^ 4 by exact Nat.pow_add 5 (4 * k) 4]
      simp
      rw [show 1 = 1 * 1 by simp]
      suffices 625 ≡ 1 [MOD 16] by exact Nat.ModEq.mul ih this
      rfl
  -- Lemma: 5^k ≡ 1 [MOD 4] for all k
  have h3 : ∀ k : ℕ, 5 ^ k ≡ 1 [MOD 4]:= by
    intro k
    rw [show 1 = 1 ^ k by simp]
    suffices 5 ≡ 1 [MOD 4] by exact Nat.ModEq.pow k this
    rfl
  -- Rewrite h3: 5^k = 4t + 1 for some t
  replace h3 : ∀ k : ℕ, ∃ t : ℕ, 5 ^ k = 4 * t + 1:= by
    intro k
    replace h3:= h3 k
    have g : 5 ^ k > 0:= by positivity
    replace g : 5 ^ k ≥ 1:= by omega
    -- 4 divides 5^k - 1, so 5^k = 4t + 1 for some t
    replace h3 : 4 ∣ 5 ^ k - 1:= by exact (Nat.modEq_iff_dvd' g).mp (id (Nat.ModEq.symm h3))
    rcases h3 with ⟨t, h3⟩
    use t
    omega
  -- Lemma: 5^(5^k) ≡ 5 [MOD 16] for all k
  replace h3 : ∀ k : ℕ, 5 ^ (5 ^ k) ≡ 1 * 5 [MOD 16]:= by
    intro k
    replace h3:= h3 k
    rcases h3 with ⟨t, h3⟩
    rw [h3]
    -- 5^(4t + 1) = 5^(4t) * 5 ≡ 1 * 5 [MOD 16]
    rw [show 5 ^ (4 * t + 1) = 5 ^ (4 * t) * 5 by ring_nf]
    replace h2:= h2 t
    exact Nat.ModEq.mul h2 rfl
  simp at h3
  -- 5^(5^k) ≡ 3125 [MOD 16] for all k
  replace h3 : ∀ k : ℕ, 5 ^ (5 ^ k) ≡ 3125 [MOD 16]:= by
    intro k
    exact h3 k
  -- Lemma: For k > 0, 5^(5^k) ≡ 3125 [MOD 625]
  replace h2 : ∀ k : ℕ, k > 0 → 5 ^ (5 ^ k) ≡ 3125 [MOD 625]:= by
    intro k hk
    suffices 5 ^ (5 ^ k) ≡ 0 [MOD 625] by exact this
    suffices 625 ∣ 5 ^ (5 ^ k) by exact Nat.modEq_zero_iff_dvd.mpr this
    set t:= k - 1 with ht
    clear_value t
    replace ht : k = t + 1:= by omega
    subst k
    ring_nf
    -- 625 = 5^4, and 5^(5^t * 5) = 5^(5^(t+1)) is divisible by 5^4 when 5^t * 5 ≥ 4
    rw [show 625 = 5 ^ 4 by simp]
    replace hk : 5 ^ t > 0:= by positivity
    replace hk : 5 ^ t ≥ 1:= by omega
    replace hk : 5 ^ t * 5 ≥ 4:= by omega
    exact Nat.pow_dvd_pow_iff_le_right'.mpr hk
  -- 16 and 625 are coprime
  have g : Nat.Coprime 16 625:= by norm_num
  -- Combine the two congruences using Chinese Remainder Theorem
  replace h2 : ∀ k : ℕ, k > 0 → 5 ^ (5 ^ k) ≡ 3125 [MOD 10000]:= by
    intro k hk
    rw [show 10000 = 16 * 625 by omega]
    replace h2:= h2 k hk
    replace h3:= h3 k
    refine (Nat.modEq_and_modEq_iff_modEq_mul g).mp ⟨h3, h2⟩
  -- Final calculation: show that (n / 1000) % 10 = 3
  suffices n / 1000 % 10 = 3 % 10 by exact this
  rw [h1]
  -- n % 10000 = 3125
  have h4 : n % 10000 = 3125:= by
    rw [hn]
    exact h2 (5 ^ m ^ m) (by positivity)
  rw [h4]
