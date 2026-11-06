import Mathlib

/-Let $k$ be a positive integer. Show that the decimal value of the binary number $(\underbrace{11\dots1}_{k})_2$,
which consists of $k$ digits all equal to 1, is $2^k-1$.-/

theorem number_theory_637388 (k: ℕ) (h: 0 < k): (Finset.range k).sum (fun i => 2^i) = 2^k - 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp [ih, Nat.pow_succ]
    rw [Finset.sum_range_succ]
    by_cases r: k = 0
    .
      simp [r]
    .
      have u: 0 < k := by omega
      apply ih at u
      rw [u]
      zify
      have v: ↑(2 ^ k - (1: ℕ)) = ↑(2 ^ k: ℕ) - ((1: ℕ): ℤ) := by
        apply Int.natCast_sub
        suffices 0 < 2 ^ k by omega
        apply Nat.pow_pos
        norm_num
      have v2: ↑(2 ^ k * 2 - (1: ℕ)) = ↑(2 ^ k * 2: ℕ) - ((1: ℕ): ℤ) := by
        apply Int.natCast_sub
        suffices 0 < 2 ^ k * 2 by omega
        apply Nat.mul_pos
        apply Nat.pow_pos
        norm_num
        norm_num
      rw [v, v2]
      simp
      ring