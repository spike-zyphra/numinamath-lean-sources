import Mathlib

/- Charlize accidentally omitted two consecutive integers when adding the elements of the arithmetic sequence, $\{1, 2, 3, \ldots, n\}$. If the sum she obtained is $241$, what is the smallest possible value of $n$? -/
theorem algebra_19665 (n m: ℕ) (h1 : n > 1) (s : ℕ) (h2 : m ≥ 1) (h3 : m ≤ n - 1) (hs : s = ∑ i in Finset.Icc 1 n, i)
    (hsum : s - m - (m + 1) = 241) : n = 23:= by
        -- h4：证明从1到k的自然数和等于 k*(k+1)/2
        have h4 (k : ℕ): ∑ i ∈ Finset.Icc 1 k, i = k * (k + 1) / 2 := by
            induction k with
            | zero =>
                simp
            | succ k ih =>
                rw [Finset.sum_Icc_succ_top (show k + 1 ≥ 1 by linarith) (fun x => x),ih]
                ring_nf
                omega
        specialize h4 n
        rw [hs,h4] at hsum
        rw [h4] at hs
        clear h4

        -- h5：证明当遗漏最小的两个连续数（1和2）时，和应大于等于241
        have h5 : n * (n + 1) / 2 - 1 - (1 + 1) ≥ 241 := by
            calc _ ≥ n * (n + 1) / 2 - m - (m + 1) := by omega
                 _ = _:= by rw [hsum]
        simp at h5

        -- h6：证明当遗漏最大的两个连续数时，和应小于等于241
        have h6 : n * (n + 1) / 2 - (n - 1) - (n - 1 + 1) ≤ 241 := by
            calc _ ≤ n * (n + 1) / 2 - m - (m + 1) := by omega
                 _ = _:= by rw [hsum]
        have hn1 : n - 1 ≥ 1 := by linarith

        -- h7：证明 n < 24
        have h7 : n < 24 := by
            by_contra! H
            clear * - h6 h1 H
            apply Nat.le_add_of_sub_le at h6
            apply Nat.le_add_of_sub_le at h6
            rw [Nat.div_le_iff_le_mul_add_pred (by simp)] at h6
            zify at h6
            rw [show ((n - 1) : ℕ) = (n : ℤ) - 1 from Int.natCast_pred_of_pos (by linarith)] at h6
            nlinarith

        -- h8：证明 n > 21
        have h8 : n > 21 := by
            by_contra! H
            have g1 :n * (n + 1) ≤ n * (21 + 1):= Nat.mul_le_mul  (show n ≤ n by simp) (show n + 1 ≤ 21 + 1 by nlinarith)
            replace g1 : n * (n + 1) / 2 ≤ n * (21 + 1) / 2:= Nat.div_le_div_right g1
            replace g1 : n * (n + 1) / 2 - 1 ≤ n * (21 + 1) / 2 - 1:= Nat.sub_le_sub_right g1 1
            replace g1 : n * (n + 1) / 2 - 1 - 2 ≤ n * (21 + 1) / 2 - 1 - 2:= Nat.sub_le_sub_right g1 2
            have g2 : n * (21 + 1) / 2 ≤ 21 * (21 + 1) / 2:= Nat.div_le_div_right (Nat.mul_le_mul (show n ≤ 21 by linarith) (show 21 + 1 ≤ 21 + 1 by simp))
            replace g2 : n * (21 + 1) / 2 - 1 ≤ 21 * (21 + 1) / 2 - 1:= Nat.sub_le_sub_right g2 1
            replace g2 : n * (21 + 1) / 2 - 1 - 2 ≤ 21 * (21 + 1) / 2 - 1 - 2:= Nat.sub_le_sub_right g2 2
            have g3 : 241 ≤ 228:= by
                calc _ ≤ n * (n + 1) / 2 - 1 - 2 := h5
                     _ ≤ n * (21 + 1) / 2 - 1 - 2 := g1
                     _ ≤ 21 * (21 + 1) / 2 - 1 - 2 := g2
                     _ = 228 := by omega
            trivial
        clear h5 h6
        replace h8 : n ≥ 22 := h8
        replace h7 : n ≤ 23 := Nat.le_of_lt_succ h7

        -- h9：证明 n ≠ 22
        have h9 : n ≠ 22:= by
            by_contra! H
            rw [H] at hsum
            simp at hsum
            have h10 : m + 1 ≤ 253 - m:= by omega
            apply (Nat.sub_eq_iff_eq_add h10).1 at hsum
            have h11 : m ≤ 253:= by omega
            apply (Nat.sub_eq_iff_eq_add h11).1 at hsum
            have h12 : 2 * m = 11:= by omega
            have h13 : 2 ∣ 11:= Dvd.intro m h12
            trivial
        -- 最终证明 n = 23
        omega
