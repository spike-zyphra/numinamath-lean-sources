import Mathlib

/- Krista put 1 cent into her new bank on a Sunday morning.  On Monday she put 2 cents into her bank.  On Tuesday she put 4 cents into her bank, and she continued to double the amount of money she put into her bank each day for two weeks.  On what day of the week did the total amount of money in her bank first exceed $\$5$? -/
theorem algebra_21151 (m k t: ℕ) (h1 : IsLeast {n : ℕ | 1 + ∑ i ∈ Finset.range (n + 1), 2 ^ i > 500} k) (h2 : t = m + k) (h3 : m % 7 = 0) : t % 7 = 1 := by
    -- 引理：计算2的幂次和的通项公式
    have h : ∀ (k : ℕ), ∑ i ∈ Finset.range k, 2 ^ i = 2 ^ k - 1:= by
        intro k
        induction k with
        | zero => simp
        | succ k hk =>
          have h1 : ∑ i ∈ Finset.range (k + 1), 2 ^ i = 2 ^ k + ∑ i ∈ Finset.range k, 2 ^ i:= Finset.sum_range_succ_comm (HPow.hPow 2) k
          rw [h1, hk]
          ring_nf
          have h2 : 2 ^ k ≥ 1:= Nat.one_le_two_pow
          replace h2 : 2 ^ k - 1 ≥ 0:= by omega
          omega
    -- 证明k=8（即第8天时总额首次超过500分钱=$5）
    have g : IsLeast {n : ℕ | 1 + ∑ i ∈ Finset.range (n + 1), 2 ^ i > 500} 8:= by
      constructor <;>
      simp [lowerBounds]
      .
        specialize h 9
        rw [h]
        norm_num
      .
        intro n hn
        specialize h (n + 1)
        rw [h] at hn
        have h1 : 2 ^ (n + 1) ≥ 1:= Nat.one_le_two_pow
        replace h1 : 2 ^ (n + 1) - 1 ≥ 0:= by omega
        have h2 : 1 + (2 ^ (n + 1) - 1) = 2 ^ (n + 1):= by omega
        rw [h2] at hn
        by_contra H
        simp at H
        replace H : n + 1 ≤ 8:= by omega
        have h3 : 2 ^ (n + 1) ≤ 2 ^ 8:= Nat.pow_le_pow_of_le_right (by omega) H
        norm_num at h3
        omega
    -- 最后证明是周日
    have h4 : k = 8:= IsLeast.unique h1 g
    rw [h4] at h2
    rw [h2]
    calc _ = (m % 7 + 8 % 7) % 7 := Nat.add_mod m 8 7  -- 使用模运算性质
         _ = (m % 7 + 1) % 7 := by omega               -- 8 % 7 = 1
         _ = (0 + 1) % 7 := by rw [h3]                -- m % 7 = 0
         _ = 1 % 7 := by omega                        -- 0 + 1 = 1
         _ = 1 := by omega                            -- 1 % 7 = 1
