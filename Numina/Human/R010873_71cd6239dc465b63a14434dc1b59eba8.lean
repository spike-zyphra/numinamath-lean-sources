import Mathlib

/- Find the number of ordered quadruples $(a,b,c,d)$ of real numbers such that
\begin{align*}
a^4 + b^4 + c^4 + d^4 &= 48, \\
abcd &= 12.
\end{align*} -/
theorem algebra_22065 :
    {(a, b, c, d) : ℝ × ℝ × ℝ × ℝ | a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4 = 48 ∧ a * b * c * d = 12}.ncard = 8 := by
    -- 第一步：证明所有满足条件的四元组中的每个数的四次方都等于12
    have h1 : ∀ n ∈ {(a, b, c, d) : ℝ × ℝ × ℝ × ℝ | a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4 = 48 ∧ a * b * c * d = 12}, (n.1) ^ 4 = 12 ∧ (n.2.1) ^ 4 = 12 ∧ (n.2.2.1) ^ 4 = 12 ∧ (n.2.2.2) ^ 4 = 12:= by
        intro n hn
        let ⟨x, y, z, w⟩ := n
        simp
        have h1 : x ^ 4 + y ^ 4 + z ^ 4 + w ^ 4 = 48 := hn.1
        have h2 : x * y * z * w = 12 := hn.2
        have h3 : x ^ 4 + y ^ 4 + z ^ 4 + w ^ 4 ≥ 2 * (x ^ 2 * y ^ 2) + 2 * (z ^ 2 * w ^ 2) := by
            calc _ = 2 * (x ^ 2 * y ^ 2) + 2 * (z ^ 2 * w ^ 2) + (x ^ 2 - y ^ 2) ^ 2 + (z ^ 2 - w ^ 2) ^ 2:= by ring
                 _ ≥ 2 * (x ^ 2 * y ^ 2) + 2 * (z ^ 2 * w ^ 2) := by
                    have _ : (z ^ 2 - w ^ 2) ^ 2 ≥ 0:= by exact sq_nonneg (z ^ 2 - w ^ 2)
                    have _ : (x ^ 2 - y ^ 2) ^ 2 ≥ 0:= by exact sq_nonneg (x ^ 2 - y ^ 2)
                    linarith
        have h11 : 2 * (x ^ 2 * y ^ 2) + 2 * (z ^ 2 * w ^ 2) ≥ 4 * (x * y * z * w):= by
            calc _ = 2 * (x * y - z * w) ^ 2 + 4 * (x * y * z * w) := by ring
                 _ ≥ 4 * (x * y * z * w):= by
                    have hxyzw : (x * y - z * w) ^ 2 ≥ 0:= by exact sq_nonneg (x * y - z * w)
                    linarith
        have h4 : x ^ 4 + y ^ 4 + z ^ 4 + w ^ 4 = 2 * (x ^ 2 * y ^ 2) + 2 * (z ^ 2 * w ^ 2):= by linarith
        replace h4 :  (x ^ 2 - y ^ 2) ^ 2 + (z ^ 2 - w ^ 2) ^ 2 = 0:= by
            ring_nf
            linarith
        replace h4 : (x ^ 2 - y ^ 2) ^ 2 = 0 ∧ (z ^ 2 - w ^ 2) ^ 2 = 0:= by
            have _ : (x ^ 2 - y ^ 2) ^ 2 ≥ 0:= by exact sq_nonneg (x ^ 2 - y ^ 2)
            have _ : (z ^ 2 - w ^ 2) ^ 2 ≥ 0:= by exact sq_nonneg (z ^ 2 - w ^ 2)
            constructor
            . linarith
            . linarith
        have h5 : x ^ 4 + y ^ 4 + z ^ 4 + w ^ 4 ≥ 2 * (x ^ 2 * z ^ 2) + 2 * (y ^ 2 * w ^ 2) := by
            calc _ = 2 * (x ^ 2 * z ^ 2) + 2 * (y ^ 2 * w ^ 2) + (x ^ 2 - z ^ 2) ^ 2 + (y ^ 2 - w ^ 2) ^ 2:= by ring
                 _ ≥ 2 * (x ^ 2 * z ^ 2) + 2 * (y ^ 2 * w ^ 2):= by
                    have _ : (x ^ 2 - z ^ 2) ^ 2 ≥ 0:= by exact sq_nonneg (x ^ 2 - z ^ 2)
                    have _ : (y ^ 2 - w ^ 2) ^ 2 ≥ 0:= by exact sq_nonneg (y ^ 2 - w ^ 2)
                    linarith
        have h12 : 2 * (x ^ 2 * z ^ 2) + 2 * (y ^ 2 * w ^ 2) ≥ 4 * (x * z * y * w):= by
            calc _ = 2 * (x * z - y * w) ^ 2 + 4 * (x * z * y * w) := by ring
                 _ ≥ 4 * (x * z * y * w):= by
                    have _ : (x * z - y * w) ^ 2 ≥ 0:= by exact sq_nonneg (x * z - y * w)
                    linarith
        have h6 : x ^ 4 + y ^ 4 + z ^ 4 + w ^ 4 = 2 * (x ^ 2 * z ^ 2) + 2 * (y ^ 2 * w ^ 2):= by linarith
        replace h6 : (x ^ 2 - z ^ 2) ^ 2 + (y ^ 2 - w ^ 2) ^ 2 = 0:= by
            ring_nf
            linarith
        replace h6 : (x ^ 2 - z ^ 2) ^ 2 = 0 ∧ (y ^ 2 - w ^ 2) ^ 2 = 0:= by
            have _ : (x ^ 2 - z ^ 2) ^ 2 ≥ 0:= by exact sq_nonneg (x ^ 2 - z ^ 2)
            have _ : (y ^ 2 - w ^ 2) ^ 2 ≥ 0:= by exact sq_nonneg (y ^ 2 - w ^ 2)
            constructor
            . linarith
            . linarith
        clear h2 h3 h5 h11 h12
        replace h4 : x ^ 2 = y ^ 2 ∧ z ^ 2 = w ^ 2:= by
            have hxy : (x ^ 2 - y ^ 2) ^ 2 = 0:= by exact h4.1
            have hzw : (z ^ 2 - w ^ 2) ^ 2 = 0:= by exact h4.2
            constructor
            .
                have _ :x ^ 2 - y ^ 2 = 0:= by exact pow_eq_zero hxy
                linarith
            .
                have _ :z ^ 2 - w ^ 2 = 0:= by exact pow_eq_zero hzw
                linarith
        replace h6 : x ^ 2 = z ^ 2 ∧ y ^ 2 = w ^ 2:= by
            have hxz : (x ^ 2 - z ^ 2) ^ 2 = 0:= by exact h6.1
            have hyw : (y ^ 2 - w ^ 2) ^ 2 = 0:= by exact h6.2
            constructor
            .
                have _ : x ^ 2 - z ^ 2 = 0:= by exact pow_eq_zero hxz
                linarith
            .
                have _ : y ^ 2 - w ^ 2 = 0:= by exact pow_eq_zero hyw
                linarith
        replace h4 : x ^ 4 = y ^ 4 ∧ z ^ 4 = w ^ 4:= by
            constructor
            .
                calc _ = (x ^ 2) ^ 2 := by ring
                     _ = (y ^ 2) ^ 2 := by rw [h4.1]
                     _ = y ^ 4 := by ring
            .
                calc _ = (z ^ 2) ^ 2 := by ring
                     _ = (w ^ 2) ^ 2 := by rw [h4.2]
                     _ = w ^ 4 := by ring
        replace h6 : x ^ 4 = z ^ 4 ∧ y ^ 4 = w ^ 4:= by
            constructor
            .
                calc _ = (x ^ 2) ^ 2 := by ring
                     _ = (z ^ 2) ^ 2 := by rw [h6.1]
                     _ = z ^ 4 := by ring
            .
                calc _ = (y ^ 2) ^ 2 := by ring
                     _ = (w ^ 2) ^ 2 := by rw [h6.2]
                     _ = w ^ 4 := by ring
        refine ⟨?_, ?_, ?_, ?_⟩
        all_goals linarith
    -- 定义m为12的四次方根
    let m := (12 : ℝ) ^ (1 / 4 : ℝ)
    have mpos : m > 0 := by positivity
    -- 证明m^4 = 12
    have hm : m ^ 4 = 12 := by
        calc _ = ((12 : ℝ) ^ (1 / 4 : ℝ)) ^ 4 := rfl
             _ = (12 : ℝ) ^ ((1 / 4 : ℝ) * (4 : ℕ)) := (Real.rpow_mul_natCast (by norm_num) (1 / 4) 4).symm
             _ = 12 := by norm_num
    -- 证明如果x^4 = 12，那么x只能等于m或-m
    have h2 (x : ℝ): x ^ 4 = 12 → x = m ∨ x = -m:= by
        intro hx
        have hy : x ^ 4 = m ^ 4 := by rw [hx, hm]
        have hz : (x ^ 2 - m ^ 2) * (x ^ 2 + m ^ 2) = 0:= by
            calc _ = x ^ 4 - m ^ 4 := by ring
                 _ = 0 := by rw [hy, sub_self]
        have hp : x ^ 2 + m ^ 2 > 0:= by
            have _ : x ^ 2 ≥ 0:= by exact sq_nonneg x
            have _ : m ^ 2 > 0:= by exact sq_pos_of_pos mpos
            linarith
        have hw : x ^ 2 - m ^ 2 = 0 ∨ x ^ 2 + m ^ 2 = 0:= by exact mul_eq_zero.mp hz
        have hl : x ^ 2 - m ^ 2 = 0:= by
            rcases hw with h1 | h2
            . exact h1
            . by_contra
              rw [h2] at hp
              simp at hp
        clear hx hy hz hp hw
        have hx : x - m = 0 ∨ x + m = 0:= by
            have hy : (x - m) * (x + m) = 0:= by
                calc _ = x ^ 2 - m ^ 2 := by ring
                     _ = 0 := by rw [hl]
            exact mul_eq_zero.mp hy
        rcases hx with h1 | h2
        .   replace h1 : x = m:= by linarith
            left
            exact h1
        .   replace h2 : x = -m:= by linarith
            right
            exact h2
    -- 证明所有满足条件的四元组都是由m和-m组成的8种组合之一
    have h3 : ∀ n ∈ {(a, b, c, d) : ℝ × ℝ × ℝ × ℝ | a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4 = 48 ∧ a * b * c * d = 12}, n ∈ {n | n = (m, m, m, m) ∨ n = (m, m, -m, -m) ∨ n = (m, -m, m, -m) ∨ n = (m, -m, -m, m) ∨ n = (-m, m, m, -m) ∨ n = (-m, m, -m, m) ∨ n = (-m, -m, m, m) ∨ n = (-m, -m, -m, -m)}:= by
        intro n hn
        specialize h1 n hn
        simp at hn
        replace hn := hn.2
        let ⟨x, y, z, w⟩ := n
        simp at h1 hn
        have hx : x = m ∨ x = -m:= by exact h2 x h1.1
        have hy : y = m ∨ y = -m:= by exact h2 y h1.2.1
        have hz : z = m ∨ z = -m:= by exact h2 z h1.2.2.1
        have hw : w = m ∨ w = -m:= by exact h2 w h1.2.2.2
        simp
        replace hn : w = m ^ 4 / (x * y * z):= by
            rw [hm, ←hn]
            have _ : (x * y * z) ≠ 0:= by
                by_contra!
                rw [this] at hn
                ring_nf at hn
                linarith
            field_simp
        have hm' : m ≠ -m:= by
            by_contra!
            replace this : m = 0:= by linarith
            linarith
        rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz <;> simp [hx, hz] at hn <;> simp [hx, hy, hz, hn, hm'] <;> field_simp <;> ring_nf <;> tauto
    -- 反向证明：这8种组合都满足原始条件
    have h4 : ∀ n ∈
    {n |
      n = (m, m, m, m) ∨
        n = (m, m, -m, -m) ∨
          n = (m, -m, m, -m) ∨
            n = (m, -m, -m, m) ∨ n = (-m, m, m, -m) ∨ n = (-m, m, -m, m) ∨ n = (-m, -m, m, m) ∨ n = (-m, -m, -m, -m)}, n ∈ {(a, b, c, d) | a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4 = 48 ∧ a * b * c * d = 12}:= by
            intro n hn
            simp at hn
            rcases hn with h11 | h11 | h11 | h11 | h11 | h11 | h11 | h11
            all_goals
            simp [h11,hm]
            constructor
            .
              linarith
            .
              linarith
    have h5 : {(a, b, c, d) | a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4 = 48 ∧ a * b * c * d = 12} = {n |
      n = (m, m, m, m) ∨
        n = (m, m, -m, -m) ∨
          n = (m, -m, m, -m) ∨
            n = (m, -m, -m, m) ∨ n = (-m, m, m, -m) ∨ n = (-m, m, -m, m) ∨ n = (-m, -m, m, m) ∨ n = (-m, -m, -m, -m)}:= by
            exact Set.Subset.antisymm h3 h4
    clear h1 h2 h3 h4 mpos hm
    rw [h5]
    clear h5

    have hm : m > 0 := by positivity
    replace hm : m ≠ -m := by linarith
    -- 最后证明集合基数为8
    change Set.ncard {(m, m, m, m), (m, m, -m, -m), (m, -m, m, -m), (m, -m, -m, m), (-m, m, m, -m), (-m, m, -m, m), (-m, -m, m, m), (-m, -m, -m, -m)} = 8

    rw [show ({(m, m, m, m), (m, m, -m, -m), (m, -m, m, -m), (m, -m, -m, m), (-m, m, m, -m), (-m, m, -m, m), (-m, -m, m, m), (-m, -m, -m, -m)} : Set (ℝ × ℝ × ℝ × ℝ)) = ({(m, m, m, m), (m, m, -m, -m), (m, -m, m, -m), (m, -m, -m, m), (-m, m, m, -m), (-m, m, -m, m), (-m, -m, m, m), (-m, -m, -m, -m)} : Finset (ℝ × ℝ × ℝ × ℝ)) by simp]
    rw [Set.ncard_coe_Finset]
    repeat rw [Finset.card_insert_of_not_mem]
    simp
    all_goals
      simp [hm]
