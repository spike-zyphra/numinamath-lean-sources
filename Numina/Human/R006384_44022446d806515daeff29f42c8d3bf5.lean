import Mathlib
/- Let $M$ be a positive integer. Determine the sum of all positive integers $n$ such that $n < M$ and $2n^2 - 3n - 2$ is a multiple of $6$. Show that this sum is equal to $k_e(k_e+1) - 3k_6(k_6+1)$, where $k_e = \lfloor (M-1)/2 \rfloor$ and $k_636493 = \lfloor (M-1)/6 \rfloor$. -/
theorem number_theory_636493 (m : ℕ) (hm : m > 0) : {n ∈ Finset.range m | n > 1 ∧ 6 ∣ 2 * n ^ 2 - 3 * n - 2}.sum (fun x => x) = ((m - 1) / 2) * ((m - 1) / 2 + 1) - 3 * ((m - 1) / 6) * ((m - 1) / 6 + 1):= by
  -- First, we prove that the set of numbers satisfying the condition
  -- is exactly the numbers congruent to 2 or 4 modulo 6
  have h1 : {n ∈ Finset.range m | n > 1 ∧ 6 ∣ 2 * n ^ 2 - 3 * n - 2} = {n ∈ Finset.range m | n ≡ 2 [MOD 6] ∨ n ≡ 4 [MOD 6]}:= by
    ext n
    constructor
    .
      -- Forward direction: if n satisfies the condition, then n ≡ 2 or 4 (mod 6)
      intro h
      simp at h
      rcases h with ⟨h1, h2, h3⟩
      simp
      refine ⟨h1, ?_⟩
      -- Let a = n - 2, so n = a + 2
      set a:= n - 2 with ha
      clear_value a
      replace ha : n = a + 2:= by omega
      subst n
      ring_nf at h3
      -- Simplify the expression 2n² - 3n - 2 = a(2a + 5)
      rw [show 8 + a * 8 + a ^ 2 * 2 - (6 + a * 3) - 2 = a * (2 * a + 5) by ring_nf ; omega] at h3
      -- Since 6 divides a(2a + 5), both 2 and 3 must divide it
      have h4 : 2 ∣ a * (2 * a + 5):= by omega
      replace h3 : 3 ∣ a * (2 * a + 5):= by omega
      have g1 : Nat.Prime 2:= by norm_num
      have g2 : Nat.Prime 3:= by norm_num
      have g3 : Nat.Coprime 2 3:= by norm_num
      -- By prime factorization, either 2 divides a or 2 divides (2a + 5)
      replace h4 : 2 ∣ a ∨ 2 ∣ 2 * a + 5:= by exact (Nat.Prime.dvd_mul g1).mp h4
      rcases h4 with h4 | h4
      .
        -- Case 1: 2 divides a
        -- Similarly, either 3 divides a or 3 divides (2a + 5)
        replace h3 : 3 ∣ a ∨ 3 ∣ 2 * a + 5:= by exact (Nat.Prime.dvd_mul g2).mp h3
        rcases h3 with h3 | h3
        .
          -- Subcase 1.1: Both 2 and 3 divide a, so 6 divides a
          replace h3 : 2 * 3 ∣ a:= by exact Nat.Coprime.mul_dvd_of_dvd_of_dvd g3 h4 h3
          simp at h3
          replace h3 : a ≡ 0 [MOD 6]:= by exact Nat.modEq_zero_iff_dvd.mpr h3
          replace h3 : a + 2 ≡ 0 + 2 [MOD 6]:= by exact Nat.ModEq.add_right 2 h3
          simp at h3
          left
          exact h3
        .
          -- Subcase 1.2: 2 divides a but 3 divides (2a + 5)
          rcases h4 with ⟨a, rfl⟩
          ring_nf at h3
          replace h3 : 3 ∣ a + 2:= by omega
          right
          -- Show that n ≡ 4 (mod 6)
          suffices 2 * a + 2 + 2 ≡ 4 + 2 [MOD 6] by exact Nat.ModEq.symm (Nat.ModEq.add_right_cancel' 2 (id (Nat.ModEq.symm this)))
          simp
          rw [show 2 * a + 2 + 2 = 2 * (a + 2) by ring]
          rcases h3 with ⟨k, hk⟩
          rw [hk]
          ring_nf
          suffices k * 6 ≡ 0 [MOD 6] by exact this
          suffices 6 ∣ k * 6 by exact Nat.modEq_zero_iff_dvd.mpr this
          simp
      .
        -- Case 2: 2 divides (2a + 5) - this leads to a contradiction
        omega
    .
      -- Reverse direction: if n ≡ 2 or 4 (mod 6), then n satisfies the condition
      intro h
      simp at h
      rcases h with ⟨h1, h2⟩
      simp
      have g : n ≥ n % 6:= by exact Nat.mod_le n 6
      rcases h2 with h2 | h2
      .
        -- Case 1: n ≡ 2 (mod 6)
        rw [h2] at g
        simp at g
        refine ⟨h1, g, ?_⟩
        -- Let a = n - 2, so n = a + 2
        set a:= n - 2 with ha
        clear_value a
        replace ha : n = a + 2:= by omega
        subst n
        -- Simplify 2n² - 3n - 2 = a(2a + 5)
        rw [show 2 * (a + 2) ^ 2 - 3 * (a + 2) - 2 = a * (2 * a + 5) by ring_nf ; omega]
        -- Since n ≡ 2 (mod 6), we have 6 divides a
        replace h2 : 6 ∣ a + 2 - 2:= by exact (Nat.modEq_iff_dvd' g).mp (id (Nat.ModEq.symm h2))
        rw [show a + 2 - 2 = a by omega] at h2
        exact Dvd.dvd.mul_right h2 (2 * a + 5)
      .
        -- Case 2: n ≡ 4 (mod 6)
        rw [h2] at g
        simp at g
        refine ⟨h1, (by omega), ?_⟩
        -- Let a = n - 2, so n = a + 2
        set a:= n - 2 with ha
        clear_value a
        replace ha : n = a + 2:= by omega
        subst n
        -- Simplify 2n² - 3n - 2 = a(2a + 5)
        rw [show 2 * (a + 2) ^ 2 - 3 * (a + 2) - 2 = a * (2 * a + 5) by ring_nf ; omega]
        -- Since n ≡ 4 (mod 6), we have 6 divides (a - 2)
        replace h2 : 6 ∣ a + 2 - 4:= by exact (Nat.modEq_iff_dvd' g).mp (id (Nat.ModEq.symm h2))
        rw [show a + 2 - 4 = a - 2 by omega] at h2
        rcases h2 with ⟨k, hk⟩
        replace hk : a = 6 * k + 2:= by omega
        subst a
        -- Show that a(2a + 5) is divisible by 6
        rw [show (6 * k + 2) * (2 * (6 * k + 2) + 5) = 6 * ((3 * k + 1) * (4 * k + 3)) by ring_nf]
        simp
  rw [h1]
  -- Let k = m - 1 and express k in terms of quotient and remainder
  set k:= m - 1 with hk
  clear_value k
  replace hk : m = k + 1:= by omega
  subst m
  have h2 : k = 6 * (k / 6) + (k % 6):= by omega
  set r:= k % 6 with hr
  clear_value r
  replace hr : r < 6:= by subst r ; refine Nat.mod_lt k (by omega)
  clear hm
  set q:= k / 6
  clear_value q
  -- Express k/2 in terms of q and r
  replace h1 : k / 2 = 3 * q + r / 2:= by subst k ; omega
  rw [h1]
  -- Simplify the target expression
  rw [show (3 * q + r / 2) * (3 * q + r / 2 + 1) - 3 * q * (q + 1) = 6 * q ^ 2 + (r / 2) * (6 * q + 1) + (r / 2) ^ 2 by ring_nf ; omega]
  subst k
  clear h1
  -- Use induction on q to prove the result
  induction q with
  | zero =>
    -- Base case: q = 0
    simp
    -- Consider all possible values of r (0 to 5)
    replace hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5:= by omega
    rcases hr with hr | hr | hr | hr | hr | hr
    all_goals
      subst r
      simp
    .
      -- For r = 0, show that no numbers in range satisfy the condition
      intro x hx h
      have g : x ≥ x % 6:= by exact Nat.mod_le x 6
      rcases h with h | h
      all_goals
        rw [h] at g
        simp at g
        omega
    all_goals
      -- For other values of r, calculate the sum directly
      simp [Finset.sum_filter, Finset.sum_range_succ]
      rfl
  | succ q ih =>
    -- Inductive step: q = q' + 1
    rw [show 6 * (q + 1) + r + 1 = 6 * q + r + 7 by omega]
    simp [Finset.sum_filter] at ih ⊢
    -- Expand the range by 6 elements
    rw [Finset.sum_range_succ]
    rw [Finset.sum_range_succ]
    rw [Finset.sum_range_succ]
    rw [Finset.sum_range_succ]
    rw [Finset.sum_range_succ]
    rw [Finset.sum_range_succ]
    rw [ih]
    -- Key lemma: the condition modulo 6 depends only on (r + n) mod 6
    have h : ∀ n : ℕ, (if 6 * q + r + n ≡ 2 [MOD 6] ∨ 6 * q + r + n ≡ 4 [MOD 6] then 6 * q + r + n else 0) = (if r + n ≡ 2 [MOD 6] ∨ r + n ≡ 4 [MOD 6] then 6 * q + r + n else 0):= by
      intro n
      by_cases h : r + n ≡ 2 [MOD 6] ∨ r + n ≡ 4 [MOD 6]
      .
        -- If r + n ≡ 2 or 4 (mod 6), then 6q + r + n ≡ 2 or 4 (mod 6)
        have g : 6 * q ≡ 0 [MOD 6]:= by
          suffices 6 ∣ 6 * q by exact Nat.modEq_zero_iff_dvd.mpr this
          simp
        have h1 : 6 * q + r + n ≡ 2 [MOD 6] ∨ 6 * q + r + n ≡ 4 [MOD 6]:= by
          rw [show 6 * q + r + n = 6 * q + (r + n) by ring]
          rcases h with h | h
          all_goals
            replace h:= Nat.ModEq.add g h
            simp at h
          .
            left
            exact h
          .
            right
            exact h
        simp [h1]
        simp [h]
      .
        -- If r + n is not ≡ 2 or 4 (mod 6), then 6q + r + n is also not
        simp [h]
        intro h1
        rw [show 6 * q + r + n = 6 * q + (r + n) by ring] at h1
        rw [show 2 = 0 + 2 by simp] at h1
        rw [show 4 = 0 + 4 by simp] at h1
        have g : 6 * q ≡ 0 [MOD 6]:= by
          suffices 6 ∣ 6 * q by exact Nat.modEq_zero_iff_dvd.mpr this
          simp
        replace h1 : r + n ≡ 2 [MOD 6] ∨ r + n ≡ 4 [MOD 6]:= by
          rcases h1 with h1 | h1
          .
            left
            exact Nat.ModEq.symm (Nat.ModEq.add_left_cancel (id (Nat.ModEq.symm g)) (id (Nat.ModEq.symm h1)))
          .
            right
            exact Nat.ModEq.symm (Nat.ModEq.add_left_cancel (id (Nat.ModEq.symm g)) (id (Nat.ModEq.symm h1)))
        trivial
    -- Apply the lemma for n = 1, 2, 3, 4, 5, 6
    rw [h 1, h 2, h 3, h 4, h 5, h 6]
    -- Consider all possible values of r (0 to 5)
    replace hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5:= by omega
    rcases hr with hr | hr | hr | hr | hr | hr
    all_goals
      subst r
      simp [Nat.ModEq]
      -- Use linear arithmetic to complete the proof
      linarith
