import Mathlib

/- Trouver tous les entiers naturels $n$ pour lesquels $2^{n}+12^{n}+2011^{n}$ est un carré parfait.-/
theorem number_theory_607548 : {n : ℕ | IsSquare (2 ^ n + 12 ^ n + 2011 ^ n)} = {1} := by
  -- If `n` is a square then `n` mod `3` is `0` or `1`.
  have lem_1 {n : ℕ} (hn : IsSquare n) : n ≡ 0 [MOD 3] ∨ n ≡ 1 [MOD 3] := by
    rcases hn with ⟨k, rfl⟩
    rw [Nat.ModEq, Nat.ModEq, Nat.mul_mod]
    have : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases k % 3 <;> norm_num
  -- If `n` is a square then `n` mod `4` is `0` or `1`.
  have lem_2 {n : ℕ} (hn : IsSquare n) : n ≡ 0 [MOD 4] ∨ n ≡ 1 [MOD 4] := by
    rcases hn with ⟨k, rfl⟩
    rw [Nat.ModEq, Nat.ModEq, Nat.mul_mod]
    have : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
    interval_cases k % 4 <;> norm_num
  ext n
  constructor
  . -- Assume that `2 ^ n + 12 ^ n + 2011 ^ n` is a square, show that `n=1`.
    intro h
    rw [Set.mem_setOf_eq] at h
    by_cases hn0 : n = 0
    . -- `n=0` is impossible.
      norm_num [hn0] at h
      rcases h with ⟨k, hk⟩
      have : Nat.sqrt 3 * Nat.sqrt 3 = 3 := by
        rw [← Nat.exists_mul_self]
        exact ⟨_, hk.symm⟩
      norm_num at this
    rcases Nat.even_or_odd n with heven | hodd
    . -- `n` is even
      rcases heven with ⟨k, hk⟩
      -- `2^n` mod `3` is `1`.
      have h1 : 2 ^ n ≡ 1 [MOD 3] := by
        rw [hk, ← two_mul, pow_mul]
        have : 2 ^ 2 ≡ 1 [MOD 3] := rfl
        have := this.pow k
        rwa [one_pow] at this
      -- `12^n` mod `3` is `0`.
      have h2 : 12 ^ n ≡ 0 [MOD 3] := by
        rw [Nat.modEq_zero_iff_dvd, show n = n - 1 + 1 by omega, pow_succ]
        have : 3 ∣ 12 := by norm_num
        exact this.mul_left _
      -- `2011^n` mod `3` is `1`.
      have h3 : 2011 ^ n ≡ 1 [MOD 3] := calc
        _ ≡ 1 ^ n [MOD 3] := by gcongr; rfl
        _ ≡ 1 [MOD 3] := by rw [one_pow]
      -- Combine above, we have `2 ^ n + 12 ^ n + 2011 ^ n` mod `3` is `2`.
      have h4 : 2 ^ n + 12 ^ n + 2011 ^ n ≡ 2 [MOD 3] := (h1.add h2).add h3
      -- Which is impossible since `2 ^ n + 12 ^ n + 2011 ^ n` is a square.
      rcases lem_1 h with H | H
      all_goals
        have := h4.symm.trans H
        norm_num [Nat.ModEq] at this
    . -- `n` is odd.
      rcases hodd with ⟨k, hk⟩
      by_cases hk0 : k = 0
      . -- `k=0`, then it's clear that `n=0`.
        rw [hk, hk0, mul_zero, zero_add, Set.mem_singleton_iff]
      -- `2^n` mod `4` is `0`.
      have h1 : 2 ^ n ≡ 0 [MOD 4] := by
        rw [Nat.modEq_zero_iff_dvd, hk, show k = k - 1 + 1 by omega, pow_succ, mul_add, pow_add, mul_assoc]
        have : 4 ∣ 2 ^ (2 * 1) * 2 := by norm_num
        exact this.mul_left _
      -- `12^n` mod `4` is `0`.
      have h2 : 12 ^ n ≡ 0 [MOD 4] := by
        rw [Nat.modEq_zero_iff_dvd, hk, show k = k - 1 + 1 by omega, pow_succ, mul_add, pow_add, mul_assoc]
        apply Dvd.dvd.mul_left
        norm_num
      -- `2011^n` mod `4` is `3`.
      have h3 : 2011 ^ n ≡ 3 [MOD 4] := calc
        _ ≡ 3 ^ n [MOD 4] := by gcongr; rfl
        _ ≡ 3 ^ (2 * k + 1) [MOD 4] := by rw [hk]
        _ ≡ _ [MOD 4] := by
          nth_rw 2 [← one_mul 3]
          rw [pow_succ]
          gcongr
          rw [pow_mul, ← one_pow k]
          gcongr
          rfl
      -- Combine above, we have `2 ^ n + 12 ^ n + 2011 ^ n` mod `4` is `3`.
      have h4 : 2 ^ n + 12 ^ n + 2011 ^ n ≡ 3 [MOD 4] := (h1.add h2).add h3
      -- Which is impossible since `2 ^ n + 12 ^ n + 2011 ^ n` is a square.
      rcases lem_2 h with H | H
      all_goals
        have := h4.symm.trans H
        norm_num [Nat.ModEq] at this
  . -- Verify that `n=1`is solution.
    intro h
    rw [Set.mem_singleton_iff] at h
    simpa [h] using ⟨45, by norm_num⟩
