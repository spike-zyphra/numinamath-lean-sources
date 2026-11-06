import Mathlib

/- How many base-10 integers are exactly 4 digits in their base-3 representation and exactly 2 digits in their base-6 representation? -/
theorem number_theory_19011 :
    Set.ncard {n : ℕ | (Nat.digits 3 n).length = 4 ∧ (Nat.digits 6 n).length = 2} = 9 := by
    -- 首先证明满足条件的数的范围
    have h1 : ∀ n ∈ {n : ℕ | (Nat.digits 3 n).length = 4 ∧ (Nat.digits 6 n).length = 2}, 27 ≤ n ∧ n ≤ 80 := by
      intro n hn
      have hl := hn.1  -- 获取3进制条件
      have hn0: n ≠ 0:= by  -- 证明n不为0
          by_contra h0
          rw [h0] at hl
          rw [Nat.digits_zero 3] at hl
          trivial
      rw [Nat.digits_len 3 n (show 1 < 3 by norm_num) hn0] at hl
      constructor
      · -- 证明下界：3³ = 27
        have h1 : 3 ^ 3 ≤ n:= Nat.pow_le_of_le_log hn0 (show 3 ≤ Nat.log 3 n by linarith)
        exact h1
      . -- 证明上界：3⁴ - 1 = 80
        have h1 : Nat.log 3 n < 4:= by linarith
        apply Nat.lt_pow_of_log_lt (show 1 < 3 by norm_num) at h1
        simp at h1
        exact Nat.le_of_lt_succ h1

    -- 证明在6进制下2位数的范围
    have h2 : ∀ n ∈ {n : ℕ | (Nat.digits 3 n).length = 4 ∧ (Nat.digits 6 n).length = 2}, 6 ≤ n ∧ n ≤ 35 := by
      intro n hn
      have hl := hn.2  -- 获取6进制条件
      have hn0: n ≠ 0:= by  -- 证明n不为0
          by_contra h0
          rw [h0] at hl
          rw [Nat.digits_zero 6] at hl
          trivial
      rw [Nat.digits_len 6 n (show 1 < 6 by norm_num) hn0] at hl
      constructor
      · -- 证明下界：6¹ = 6
        have h1 : 6 ^ 1 ≤ n:= Nat.pow_le_of_le_log hn0 (show 1 ≤ Nat.log 6 n by linarith)
        exact h1
      . -- 证明上界：6² - 1 = 35
        have h1 : Nat.log 6 n < 2:= by linarith
        apply Nat.lt_pow_of_log_lt (show 1 < 6 by norm_num) at h1
        simp at h1
        exact Nat.le_of_lt_succ h1

    -- 结合h1和h2，得到最终范围[27, 35]
    have h3 : ∀ n ∈ {n : ℕ | (Nat.digits 3 n).length = 4 ∧ (Nat.digits 6 n).length = 2}, 27 ≤ n ∧ n ≤ 35 := by
      intro n hn
      specialize h1 n hn
      specialize h2 n hn
      replace h1 := h1.1
      replace h2 := h2.2
      exact ⟨h1, h2⟩
    clear h1 h2

    -- 证明满足条件的集合是[27, 35]的子集
    have h4 : ∀ n ∈ {n : ℕ | (Nat.digits 3 n).length = 4 ∧ (Nat.digits 6 n).length = 2}, n ∈ {n : ℕ | 27 ≤ n ∧ n ≤ 35}:= by
      intro n hn
      specialize h3 n hn
      exact h3
    clear h3
    rw [←Set.subset_def] at h4

    -- 将集合转换为有限集
    have H : {n | 27 ≤ n ∧ n ≤ 35} = ↑(Finset.Icc 27 35) := by
      simp [Set.Icc]

    -- 证明[27, 35]包含9个数
    have h7 : {n | 27 ≤ n ∧ n ≤ 35}.ncard = 9:= by
      rw [H, Set.ncard_coe_Finset]
      simp

    -- 证明[27, 35]中的所有数都满足原始条件
    have h5 : {n | 27 ≤ n ∧ n ≤ 35} ⊆ {n | (Nat.digits 3 n).length = 4 ∧ (Nat.digits 6 n).length = 2}:= by
      intro n hn
      simp at hn
      simp
      constructor
      . -- 证明这些数在3进制下都是4位数
        rw [Nat.digits_len 3 n (show 1 < 3 by norm_num) (show n ≠ 0 by linarith)]
        simp
        have h1 : n < 3 ^ (3 + 1):= by
            ring_nf
            linarith
        exact Nat.log_eq_of_pow_le_of_lt_pow (show 3 ^ 3 ≤ n by exact hn.1) h1
      . -- 证明这些数在6进制下都是2位数
        rw [Nat.digits_len 6 n (show 1 < 6 by norm_num) (show n ≠ 0 by linarith)]
        simp
        replace h1 : 6 ^ 1 ≤ n:= by linarith
        replace h2 : n < 6 ^ (1 + 1):= by
            ring_nf
            linarith
        exact Nat.log_eq_of_pow_le_of_lt_pow h1 h2

    -- 最终证明两个集合相等
    have h6 : {n | (Nat.digits 3 n).length = 4 ∧ (Nat.digits 6 n).length = 2} = {n | 27 ≤ n ∧ n ≤ 35} := Set.Subset.antisymm h4 h5
    rw [h6]
    exact h7
