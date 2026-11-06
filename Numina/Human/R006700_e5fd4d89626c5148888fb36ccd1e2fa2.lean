import Mathlib
/- Let $K$ be a positive integer. Find all natural numbers $n$ such that $\lfloor n/8 \rfloor + (n \pmod 9) = K$.
Show that the set of such natural numbers $n$ is empty if $K \pmod 9 = 8$.
Otherwise, show that the set of such natural numbers $n$ is $\{8q + (K \pmod 9) \mid q \in \mathbb{Z}, \max(0, K-8) \le q \le K\}$.
(This implies that if $K \pmod 9 \neq 8$, there are $9$ solutions if $K \ge 8$, and $K+1$ solutions if $K < 8$.) -/
theorem number_theory_640293 (k : ℕ) (hk : k > 0) : (k ≡ 8 [MOD 9] → {n : ℕ | n / 8 + n % 9 = k} = ∅) ∧ (¬(k ≡ 8 [MOD 9]) → {n : ℕ | n / 8 + n % 9 = k} = {n : ℕ | ∃ q : ℕ, k - 8 ≤ q ∧ q ≤ k ∧ n = 8 * q + k % 9}):= by
  constructor
  .
    -- Case 1: k ≡ 8 (mod 9) implies no solutions exist
    intro h
    -- k ≥ k mod 9 by properties of modulo
    have g : k ≥ k % 9:= by exact Nat.mod_le k 9
    rw [h] at g
    simp at g
    ext x
    -- Since k ≡ 8 (mod 9), we have 9 | (k - 8)
    replace h : 9 ∣ k - 8:= by exact (Nat.modEq_iff_dvd' g).mp (id (Nat.ModEq.symm h))
    rcases h with ⟨q, hq⟩
    -- Express k as k = 9q + 8
    replace hq : k = 9 * q + 8:= by omega
    subst k
    constructor
    .
      -- Show that no x satisfies the equation
      intro h1
      simp at h1 ⊢
      -- Prove that x/8 + x ≡ 8 (mod 9)
      have h2 : x / 8 + x ≡ 8 [MOD 9]:= by
        replace h1 : x / 8 + x % 9 ≡ 9 * q + 8 [MOD 9]:= by rw [h1]
        -- x mod 9 ≡ x (mod 9)
        have h2 : x % 9 ≡ x [MOD 9]:= by exact Nat.mod_modEq x 9
        replace h2 : x / 8 + x % 9 ≡ x / 8 + x [MOD 9]:= by exact Nat.ModEq.add rfl h2
        -- 9q ≡ 0 (mod 9)
        have h3 : 9 * q ≡ 0 [MOD 9]:= by
          suffices 9 ∣ 9 * q by exact Nat.modEq_zero_iff_dvd.mpr this
          simp
        replace h3 : 9 * q + 8 ≡ 0 + 8 [MOD 9]:= by exact Nat.ModEq.add_right 8 h3
        simp at h3
        replace h1 : x / 8 + x % 9 ≡ 8 [MOD 9]:= by exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm h3)) (id (Nat.ModEq.symm h1)))
        exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm h1)) h2)
      -- Express x as x = 8t + r where r < 8
      have h3 : x = 8 * (x / 8) + x % 8:= by omega
      set t:= x / 8
      set r:= x % 8 with hr
      clear_value t r
      replace hr : r < 8:= by subst r ; refine Nat.mod_lt x (by omega)
      rw [h3] at h2
      rw [show t + (8 * t + r) = 9 * t + r by ring] at h2
      -- 9t ≡ 0 (mod 9)
      have h4 : 9 * t ≡ 0 [MOD 9]:= by
        suffices 9 ∣ 9 * t by exact Nat.modEq_zero_iff_dvd.mpr this
        simp
      replace h4 : 9 * t + r ≡ 0 + r [MOD 9]:= by exact Nat.ModEq.add_right r h4
      simp at h4
      replace h2 : r ≡ 8 [MOD 9]:= by exact Nat.ModEq.trans (id (Nat.ModEq.symm h4)) h2
      replace h2 : r % 9 = 8:= by rw [h2]
      -- Since r < 8, r mod 9 = r, leading to contradiction
      rw [show r % 9 = r by refine Nat.mod_eq_of_lt (by omega)] at h2
      linarith
    .
      -- Empty set has no elements
      simp
  .
    -- Case 2: k ≢ 8 (mod 9) implies solutions exist
    intro h
    ext x
    constructor
    .
      -- Show that if x satisfies the equation, then x is in the solution set
      intro h1
      simp at h1 ⊢
      -- Express x as x = 8q + r where r < 8
      have h2 : x = 8 * (x / 8) + x % 8:= by omega
      set q:= x / 8
      set r:= x % 8 with hr
      clear_value q r
      replace hr : r < 8:= by subst r ; refine Nat.mod_lt x (by omega)
      subst x
      use q
      -- Prove that r = k mod 9
      have h2 : r = k % 9:= by
        replace h1 : q + (8 * q + r) % 9 ≡ k [MOD 9]:= by rw [h1]
        -- (8q + r) mod 9 ≡ (8q + r) (mod 9)
        have h2 : (8 * q + r) % 9 ≡ (8 * q + r) [MOD 9]:= by exact Nat.mod_modEq (8 * q + r) 9
        replace h2 : q + (8 * q + r) % 9 ≡ q + (8 * q + r) [MOD 9]:= by exact Nat.ModEq.add rfl h2
        rw [show q + (8 * q + r) = 9 * q + r by ring] at h2
        replace h1 : 9 * q + r ≡ k [MOD 9]:= by exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm h1)) h2)
        -- 9q ≡ 0 (mod 9)
        have h3 : 9 * q ≡ 0 [MOD 9]:= by
          suffices 9 ∣ 9 * q by exact Nat.modEq_zero_iff_dvd.mpr this
          simp
        replace h3 : 9 * q + r ≡ 0 + r [MOD 9]:= by exact Nat.ModEq.add_right r h3
        simp at h3
        replace h1 : r ≡ k [MOD 9]:= by exact Nat.ModEq.trans (id (Nat.ModEq.symm h3)) h1
        replace h1 : r % 9 = k % 9:= h1
        -- Since r < 8, r mod 9 = r
        rw [show r % 9 = r by refine Nat.mod_eq_of_lt (by omega)] at h1
        exact h1
      -- Prove the bounds on q: k ≤ q + 8 and k ≥ q
      have h3 : k ≤ q + 8:= by
        have g : (8 * q + r) % 9 < 9:= by refine Nat.mod_lt (8 * q + r) (by omega)
        linarith
      have h4 : k ≥ q:= by omega
      subst r
      refine ⟨h3, h4, rfl⟩
    .
      -- Show that if x is in the solution set, then x satisfies the equation
      intro h1
      simp at h1 ⊢
      rcases h1 with ⟨q, h0, h2, h3⟩
      -- Prove that k mod 9 < 8 (since k ≢ 8 (mod 9))
      have h1 : k % 9 < 8:= by
        by_contra H
        simp at H
        have h4 : k % 9 < 9:= by refine Nat.mod_lt k (by omega)
        replace H : k % 9 = 8:= by omega
        absurd h
        exact H
      -- Prove that x/8 = q
      have h4 : x / 8 = q:= by
        subst x
        omega
      set r:= k % 9 with hr
      clear_value r
      subst x
      rw [h4]
      -- Helper lemma: if m/9 = n/9 and m mod 9 = n mod 9, then m = n
      have h5 : ∀ m n : ℕ, m / 9 = n / 9 → m % 9 = n % 9 → m = n:= by
        intro m n hm hn
        omega
      -- Prove that (q + (8q + r) mod 9) mod 9 = r
      replace h4 : (q + (8 * q + r) % 9) % 9 = r:= by
        have h4 : (8 * q + r) % 9 ≡ (8 * q + r) [MOD 9]:= by exact Nat.mod_modEq (8 * q + r) 9
        replace h4 : q + (8 * q + r) % 9 ≡ q + (8 * q + r) [MOD 9]:= by exact Nat.ModEq.add rfl h4
        rw [show q + (8 * q + r) = 9 * q + r by ring] at h4
        -- 9q ≡ 0 (mod 9)
        have h5 : 9 * q ≡ 0 [MOD 9]:= by
          suffices 9 ∣ 9 * q by exact Nat.modEq_zero_iff_dvd.mpr this
          simp
        replace h5 : 9 * q + r ≡ 0 + r [MOD 9]:= by exact Nat.ModEq.add_right r h5
        simp at h5
        replace h4 : q + (8 * q + r) % 9 ≡ r [MOD 9]:= by exact Nat.ModEq.symm (Nat.ModEq.trans (id (Nat.ModEq.symm h5)) (id (Nat.ModEq.symm h4)))
        rw [h4]
        refine Nat.mod_eq_of_lt (by omega)
      -- Prove that (q + (8q + r) mod 9) / 9 = k / 9
      have h6 : (q + (8 * q + r) % 9) / 9 = k / 9:= by omega
      -- Apply the helper lemma to conclude q + (8q + r) mod 9 = k
      exact h5 (q + (8 * q + r) % 9) k h6 (by rw [←hr] ; exact h4)
