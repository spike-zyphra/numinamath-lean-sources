import Mathlib

/- Find all natural numbers $n$ such that $5^{n}+12^{n}$ is perfect square. -/
theorem number_theory_604354 (n : ℕ) :
    IsSquare (5^n + 12^n) ↔ n = 2 := by

  constructor
  . -- Assuming that 5 ^ n + 12 ^ n is a perfect square, we show that n = 2.
    rintro ⟨ x, hx ⟩
    rw [← pow_two] at hx
    zify at hx

    -- We consider two cases, depending on whether n is even or odd.
    rcases Nat.even_or_odd n with hEven | hOdd
    . -- Case 1: n is even. Then n = 2 * k for some k ∈ ℕ.
      obtain ⟨ k, hk ⟩ := hEven

      -- We prove a technical result showing that if a, b, c ∈ ℕ and a ^ 2 + b ^ 2 = c ^ 2,
      -- then b ≤ c and a ^ 2 = (c - b) * (c + b).
      have tech {a b c : ℕ} (h : a ^ 2 + b ^ 2 = c ^ 2) : b ≤ c ∧ a ^ 2 = (c - b) * (c + b) := by
        -- First show that b ^ 2 ≤ c ^ 2.
        have this : b ^ 2 ≤ c ^ 2 := by rw [add_comm] at h; exact Nat.le.intro h
        zify at this
        -- From this we obtain that |b| ≤ |c|. But b and c are natural numbers.
        -- Hence, |b| = b and |c| = c and so b ≤ c.
        rw [sq_le_sq] at this
        norm_cast at this
        constructor
        . exact this
        . -- Since b ≤ c implies c - b ≥ 0, we can check a ^ 2 = (c - b) * (c + b) over ℤ.
          zify
          rw [Int.ofNat_sub this]
          ring_nf
          suffices a ^ 2 + (b : ℤ) ^ 2 = c ^ 2 by symm; rw [sub_eq_iff_eq_add]; norm_cast; rw [← h]
          norm_cast

      -- Using the above result with a = 5 ^ k, b = 12 ^ k and c = x,
      -- we have that 12 ^ k ≤ x and  5 ^ (2 * k) = (x - 12 ^ k) * (x + 12 ^ k).
      have claim : 12 ^ k ≤ x ∧ 5 ^ (2 * k) = (x - 12 ^ k) * (x + 12 ^ k) := by
        rw [hk] at hx
        norm_cast at hx
        have : 5 ^ (k + k) = (5 ^ k) ^ 2 := by rw [pow_add, pow_two]
        rw [this] at hx
        have : 5 ^ (2 * k) = (5 ^ k) ^ 2 := by rw [← this]; ring
        rw [this]
        have : 12 ^ (k + k) = (12 ^ k) ^ 2 := by rw [pow_add, pow_two]
        rw [this] at hx
        exact tech hx

      -- Let xineq denote 12 ^ k ≤ x and let fac denote (x - 12 ^ k) * (x + 12 ^ k).
      obtain ⟨ xineq, fac ⟩ := claim

      -- We consider two cases depending on whether k is 0 or not.
      by_cases kZero : k = 0
      . -- When k = 0, the proof reduces to having 2 being a perfect square in the assumption, which is absurd.
        simp [kZero] at hk
        simp [hk] at hx
        norm_cast at hx
        by_contra
        have : ¬IsSquare 2 := by refine Prime.not_square ?hp; refine Nat.prime_iff.mp ?hp.a; exact Nat.prime_two
        apply this
        use x
        rw [← pow_two]
        exact hx
      . -- Now consider the case when k ≠ 0.
        -- We consider two cases, depending on whether 5 divides both x - 12 ^ k and x + 12 ^ k or not.
        by_cases h : 5 ∣ ((x - 12 ^ k) : ℤ) ∧ 5 ∣ ((x + 12 ^ k) : ℤ)
        . -- If 5 divides both x - 12 ^ k and x + 12 ^ k, then 5 divides
          -- (x + 12 ^ k) - (x - 12 ^ k) = 2 * 12 ^ k.
          -- Since gcd(5, 2) = 1, 5 must divide 12 ^ k, and therefore 5 must divide 5, which is impossible.
          obtain ⟨ hl, hr ⟩ := h
          have : 5 ∣ ((x + 12 ^ k) : ℤ) - ((x - 12 ^ k) : ℤ) := by exact Int.dvd_sub hr hl
          ring_nf at this
          have : 5 ∣ ((12 ^ k) : ℤ) := by exact Int.dvd_of_dvd_mul_left_of_gcd_one this rfl
          norm_cast at this
          have : 5 ∣ 12 := by apply Nat.Prime.dvd_of_dvd_pow
                              . exact Nat.prime_five
                              . apply this
          by_contra
          revert this
          decide
        . -- Hence, 5 divides either x - 12 ^ k or x + 12 ^ k but not both.
          -- In this case, we must have x - 12 ^ k = 1 and x + 12 ^ k = 5 ^ (2 * k).
          have : x - 12 ^ k = 1 ∧ x + 12 ^ k = 5 ^ (2 * k) := by
            push_neg at h
            by_cases g : 5 ∣ (x - 12 ^ k : ℤ)
            . apply h at g
              norm_cast at g
              have : x + 12 ^ k ∣ 5 ^ (2 * k):= by exact Dvd.intro_left (x - 12 ^ k) (id (Eq.symm fac))
              rw [Nat.dvd_prime_pow] at this
              . obtain ⟨ q, ⟨ hql, hqr ⟩  ⟩ := this
                rw [hqr] at g
                have : q = 0 := by by_contra qc
                                   apply g
                                   exact dvd_pow_self 5 qc
                simp [this] at hqr
                simp [hqr] at fac
                have : 5 ^ (2 * k) < 1 := by
                  calc
                    _ = x - 12 ^ k := fac
                    _ < x + 12 ^ k := by apply Nat.lt_add_right (12 ^ k); refine Nat.sub_lt_of_pos_le ?h₀ xineq; exact Fin.pos'
                    _ = _ := by rw [hqr]
                simp at this
              . exact Nat.prime_five
            . norm_cast at g
              have : x - 12 ^ k ∣ 5 ^ (2 * k):= by exact Dvd.intro (x + 12 ^ k) (id (Eq.symm fac))
              rw [Nat.dvd_prime_pow] at this
              . obtain ⟨ q, ⟨ hql, hqr ⟩  ⟩ := this
                rw [hqr] at g
                have : q = 0 := by by_contra qc
                                   apply g
                                   exact dvd_pow_self 5 qc
                simp [this] at hqr
                simp [hqr] at fac
                exact ⟨hqr, id (Eq.symm fac)⟩
              . exact Nat.prime_five

          -- Since k is a nonzero natural number, we must have k ≥ 1.
          -- Hence, there exists m such that k = m + 1.
          have : ∃ m : ℕ, k = m + 1 := by exact Nat.exists_eq_succ_of_ne_zero kZero
          obtain ⟨ m, hm ⟩ := this
          -- We consider two cases, depending on whether m = 0 or not.
          by_cases mZero : m = 0
          . -- When m = 0, we have n = 2, as desired.
            rw [mZero] at hm
            rw [hm] at hk
            simp [hk]
          . -- Now consider that m ≥ 1.
            -- Since x - 12 ^ k = 1 and x + 12 ^ k = 5 ^ (2 * k), we have
            -- 5 ^ (2 * k) - 1 = x + 12 ^ k - (x - 12 ^ k) over ℤ.
            obtain ⟨ f1 , f2 ⟩ := this
            zify at f1 f2
            have claim3 : (5 ^ (2 * k) : ℤ) - 1 = ↑x + 12 ^k - (↑x - 12 ^ k) := by
              refine Lean.Omega.Int.sub_congr (id (Eq.symm f2)) ?h₂
              rw [← f1]
              rw [Int.ofNat_sub]
              . rw [@sub_eq_sub_iff_add_eq_add]
                norm_cast
              . exact xineq

            ring_nf at claim3

            -- We now proceed by contradiction.
            by_contra
            -- It suffices to show that 12 ^ k * 2 > 12 ^ k * 2, which is clearly false.
            suffices ((12 ^ k) : ℤ) * 2 > (12 ^ k * 2 : ℤ) by exact (lt_self_iff_false (12 ^ k * 2)).mp this

            -- We first show by induction on r ∈ N that -1 + 5 ^ ((r + 2) * 2)) > 24 ^ (r + 2) over ℤ.
            have claim4 {r : ℕ} : (- (1 : ℤ) + 5 ^ ((r + 2) * 2)) > (24 ^ (r + 2) : ℤ) := by
              induction r with
              | zero => simp
              | succ r ih => calc
                              _ = -1 + 5 ^ ((r + 2) * 2 + 2) := by ring
                              _ = -1 + 5 ^ ((r + 2) * 2) * 5 ^ 2 := by rw [pow_add]
                              _ = -1 + (5 ^ ((r + 2) * 2) - 1 + 1) * 5 ^ 2 := by norm_num
                              _ = (-(1 : ℤ) + 5 ^ ((r + 2) * 2)) * 5 ^ 2 + 24 := by ring
                              _ > (-(1 : ℤ) + 5 ^ ((r + 2) * 2)) * 5 ^ 2 + 0 := by apply Int.add_lt_add_left
                                                                                   norm_num
                              _ = (-(1 : ℤ) + 5 ^ ((r + 2) * 2)) * 5 ^ 2 := by rw [add_zero]
                              _ > 24 ^ (r + 2) * 5 ^ 2 := by apply Int.mul_lt_mul_of_pos_right
                                                             . exact ih
                                                             . norm_num
                              _ ≥ 24 ^ (r + 2) * 24 := by apply Int.mul_le_mul
                                                          . rfl
                                                          . norm_num
                                                          . norm_num
                                                          . apply pow_nonneg; norm_num
                              _ = _ := by ring
            -- Since m ≥ 1 and k = m + 1, we have that k = r + 2 for some r ∈ ℕ.
            -- Then from the claims above, we obtain that
            -- 12 ^ k * 2 = -1 + 5 ^ (k + 2) > 24 ^ k = 12 ^ k * 2 ^ k ≥ 12 ^ k, as desired.
            calc
              _ = -(1 : ℤ)  + 5 ^ (k * 2) := by rw [claim3]
              _ > 24 ^ k := by have : ∃ r : ℕ, k = r + 2 := by use (m - 1)
                                                               symm
                                                               calc
                                                                 _ = m - 1 + 1 + 1 := by norm_num
                                                                 _ = m + 0 + 1 := by rw [Nat.sub_one_add_one mZero]
                                                                 _ = _ := Eq.symm hm
                               obtain ⟨ r, hr ⟩ := this
                               rw [hr]
                               apply claim4
              _ = (12 * 2) ^ k := by norm_num
              _ = 12 ^ k * 2 ^ k := by apply mul_pow
              _ ≥ 12 ^ k * 2 := by apply Int.mul_le_mul_of_nonneg_left
                                   . rw [hm, pow_add, pow_one]
                                     apply Int.le_mul_of_ediv_le
                                     . norm_num
                                     . decide
                                     simp
                                     norm_cast
                                     exact Nat.one_le_two_pow
                                   . apply pow_nonneg; norm_num
    . -- Case 2: n is odd.  Then n = 2 * k + 1 for some k ∈ ℕ.
      obtain ⟨ k, hk ⟩ := hOdd

      -- We first establish two claims.
      -- The first is that x ^ 2 ≡ (-1)^k * 2 [ZMOD 5].
      have claim1 : x ^ 2 ≡ (-1)^k * 2 [ZMOD 5] := by
        rw [← hx]
        rw [hk]
        have h5 : 5 ^ (2 * k + 1) ≡ 0 [ZMOD 5] := by
          calc
            _ = 5 ^ (2 * k) * 5 := by rw [pow_add, pow_one]
            _ ≡ 0 [ZMOD 5] := by refine Dvd.dvd.modEq_zero_int ?_
                                 apply Int.dvd_mul_left
        have h12 : 12 ^ (2 * k + 1) ≡ (-1)^k * 2 [ZMOD 5] := by
          calc
            _ = 12 ^ (2 * k) * 12 := by rw [pow_add, pow_one]
            _ ≡ (12 ^ 2) ^ k * 12 [ZMOD 5] := by rw [pow_mul]
            _ ≡ (12 ^ 2) ^ k * 2 [ZMOD 5] := by exact Int.ModEq.mul_left ((12 ^ 2) ^ k) rfl
            _ ≡ (144) ^ k * 2 [ZMOD 5] := by norm_num
            _ ≡ (-1) ^ k * 2 [ZMOD 5] := by suffices 144 ≡ (-1) [ZMOD 5] by apply Int.ModEq.mul
                                                                            exact Int.ModEq.pow k this
                                                                            exact rfl
                                            exact rfl
        calc
          _ ≡ 0 + 12 ^ (2 * k + 1) [ZMOD 5] := by exact Int.ModEq.add h5 rfl
          _ = 12 ^ (2 * k + 1) := by rw [zero_add]
          _ ≡ _ [ZMOD 5] := by exact h12

      -- The second is that x ^ 2 ≡ 0 [ZMOD 5] ∨ x ^ 2 ≡ 1 [ZMOD 5] ∨ x ^ 2 ≡ 4 [ZMOD 5].
      have claim2 : x ^ 2 ≡ 0 [ZMOD 5] ∨ x ^ 2 ≡ 1 [ZMOD 5] ∨ x ^ 2 ≡ 4 [ZMOD 5]:= by
        mod_cases (x : ℤ) % 5
        . left
          rw [@Int.modEq_zero_iff_dvd]
          refine Dvd.dvd.pow ?h.hab ?h.x
          . exact Int.dvd_of_emod_eq_zero H
          . norm_num
        . right; left
          apply (Int.ModEq.pow 2) at H; simpa [H]
        . right; right
          apply (Int.ModEq.pow 2) at H; simpa [H]
        . right; right
          apply (Int.ModEq.pow 2) at H; simpa [H]
        . right; left
          apply (Int.ModEq.pow 2) at H; simpa [H]

      -- We also have that (-1) ^ r * 2 ≡ 2 [ZMOD 5] for even r.
      have claimEven {r : ℕ} (hr : Even r) : (-1)^r * 2 ≡ 2 [ZMOD 5] := by
        obtain ⟨ p, hp ⟩ := hr
        rw [hp]
        calc
         _ = (-1)^ (2 * p) * 2 := by ring
         _ = ((-1) ^ 2) ^ p * 2 := by rw [pow_mul]
         _ = 2 := by ring
         _ ≡ 2 [ZMOD 5] := by exact rfl

      -- We also have that (-1) ^ r * 2 ≡ -2 [ZMOD 5] for odd r.
      have claimOdd {r : ℕ} (hr : Odd r) : (-1)^r * 2 ≡ -2 [ZMOD 5] := by
        obtain ⟨ p, hp ⟩ := hr
        rw [hp]
        calc
         _ = (-1)^ (2 * p + 1) * 2 := by ring
         _ = (-1)^ (2 * p) * (-1) ^ 1 * 2 := by rw [pow_add]
         _ = ((-1) ^ 2) ^ p * (-1) * 2 := by rw [pow_one, pow_mul]
         _ = -2 := by ring
         _ ≡ -2 [ZMOD 5] := by exact rfl

      -- From the second claim, we split into three cases.
      rcases claim2 with h | h | h
      . -- The first case is x ^ 2 ≡ 0 [ZMOD 5] ∨ x ^ 2 ≡ 1 [ZMOD 5] ∨ x ^ 2 ≡ 4 [ZMOD 5].
        -- It follows from the first claim that 0 ≡ (-1) ^ k * 2 [ZMOD 5], which is impossible.
        have : 0 ≡ (-1) ^ k * 2 [ZMOD 5] := by exact Int.ModEq.trans (id (Int.ModEq.symm h)) claim1
        rcases Nat.even_or_odd k with hE | hO
        . have : 0 ≡ 2 [ZMOD 5] := by exact Int.ModEq.trans this (claimEven hE)
          by_contra; revert this; decide
        . have : 0 ≡ -2 [ZMOD 5] := by exact Int.ModEq.trans this (claimOdd hO)
          by_contra; revert this; decide;
      . -- The second case is x ^ 2 ≡ 1 [ZMOD 5] ∨ x ^ 2 ≡ 4 [ZMOD 5].
        -- It follows from the first claim that 1 ≡ (-1) ^ k * 2 [ZMOD 5], which is impossible.
        have : 1 ≡ (-1) ^ k * 2 [ZMOD 5] := by exact Int.ModEq.trans (id (Int.ModEq.symm h)) claim1
        rcases Nat.even_or_odd k with hE | hO
        . have : 1 ≡ 2 [ZMOD 5] := by exact Int.ModEq.trans this (claimEven hE)
          by_contra; revert this; decide
        . have : 1 ≡ -2 [ZMOD 5] := by exact Int.ModEq.trans this (claimOdd hO)
          by_contra; revert this; decide;
      . -- The third case is x ^ 2 ≡ 4 [ZMOD 5].
        -- It follows from the first claim that 4 ≡ (-1) ^ k * 2 [ZMOD 5], which is impossible.
        have : 4 ≡ (-1) ^ k * 2 [ZMOD 5] := by exact Int.ModEq.trans (id (Int.ModEq.symm h)) claim1
        rcases Nat.even_or_odd k with hE | hO
        . have : 4 ≡ 2 [ZMOD 5] := by exact Int.ModEq.trans this (claimEven hE)
          by_contra; revert this; decide
        . have : 4 ≡ -2 [ZMOD 5] := by exact Int.ModEq.trans this (claimOdd hO)
          by_contra; revert this; decide;

  . -- When n = 2, 5 ^ n + 12 ^ n = 13 ^ 2, and is therefore a square.
    intro hn
    rw [hn]
    use 13
    norm_num