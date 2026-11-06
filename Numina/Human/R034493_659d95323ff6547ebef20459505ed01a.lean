import Mathlib

/- 1. Compute the sum of all positive integers $n$ for which the expression
$$
\frac{n+7}{\sqrt{n-1}}
$$
is an integer. -/
theorem number_theory_176638 (s : Finset ℕ)(hs : s = {n : ℕ | 2 ≤ n ∧ ∃ k : ℤ, (n + 7) / Real.sqrt (n - 1) = k}):
    ∑ n ∈ s , n = 89 := by
      -- Step 1: Define the set `s` as the set of positive integers satisfying the given condition.
      have h : s = {2, 5, 17, 65} := by
        ext n
        constructor
        -- Step 2: Prove that if `n` is in `s`, then it must be one of {2, 5, 17, 65}.
        · intro hn
          have : n ∈ (s : Set ℕ) := by norm_cast
          rw [hs] at this
          simp at this
          rcases this with ⟨hge, ⟨k, hk⟩⟩
          -- Step 3: Use the fact that \(\sqrt{n-1}\) squared is \(n-1\).
          have hpow2 : √(n-1) ^ 2 = n - 1 := by
            apply Real.sq_sqrt
            norm_num
            linarith
          -- Step 4: Show that \(\sqrt{n-1}\) is an integer.
          have hN : ∃ l : ℤ, √(↑n - 1) = l := by
            have heq1 : √(n-1) = (n+7)/k := by
              rw [← hk]
              symm
              rw [div_div_cancel₀]
              linarith
            have hq : ∃ (r:ℚ), √(↑n - 1) = r := by
              rw [heq1]
              have : ∃ (r1:ℚ), (n:ℝ) + 7 = r1 := by
                use (n + 7)
                norm_cast
              rcases this with ⟨r1, hr1⟩
              have : ∃ (r2:ℚ), (k:ℝ) = r2 := by
                use k
                norm_num
              rcases this with ⟨r2, hr2⟩
              use r1 / r2
              rw [hr1, hr2]
              norm_cast
            rcases hq with ⟨r, hr⟩
            have hr' : (n:ℝ) - 1 = r ^ 2 := by
              rw [← hr, hpow2]
            have hreq : r = r.num / r.den := by exact Eq.symm (Rat.num_div_den r)
            rw [hreq] at hr'
            norm_cast at hr'
            have : ((Int.subNatNat n 1):ℚ).den = 1 := by
              exact rfl
            rw [hr'] at this
            simp at this
            have : r.den = 1 := Nat.eq_one_of_mul_eq_one_left this
            use r.num
            rw [hr, hreq, this]
            norm_num
          rcases hN with ⟨l, hl⟩
          -- Step 5: Express \(n\) in terms of \(l\).
          have hneq : (n :ℝ) = l ^ 2 + 1 := by
            calc
              _ = (n:ℝ) - 1 + 1 := by ring
              _ = √(n - 1) ^ 2 + 1 := by rw [hpow2]
              _ = _ := by rw [hl]
          have hlpos : l > 0 := by
            have : (l : ℝ) > 0 := by
              rw [← hl]
              apply Real.sqrt_pos_of_pos
              norm_num
              linarith
            norm_cast at this
          -- Step 6: Derive another equation for \(k\) in terms of \(l\).
          have : (n:ℝ) + 7 = l^2 + 8 := by
            calc
              _ = (n:ℝ) - 1 + 8 := by ring_nf
              _  = √(n-1) ^ 2 + 8 := by rw [hpow2]
              _ = _ := by rw [hl]
          rw [this, hl] at hk
          have : (k:ℝ) = l + 8 / l := by
            calc
              _ = ((l:ℝ) ^ 2 + 8) / l := by rw [← hk]
              _ = l ^ 2 / l + 8 / l := add_div ((l:ℝ) ^ 2) 8 l
              _ = _ := by
                rw [@sq]
                rw [mul_div_cancel_of_imp (congrArg fun a => a)]
          -- Step 7: Prove that \(8/l\) is an integer and derive conditions on \(l\).
          have : ∃ m : ℤ, (8:ℝ) / l = m := by
            use k - l
            calc
              _ = l + (8:ℝ) / l - l := by ring
              _ = _ := by
                rw [← this]
                norm_cast
          rcases this with ⟨m, hm⟩
          have hmpos : m ≥ 0 := by
            have : (m:ℝ) ≥ 0 := by
              rw [← hm]
              have h_1 : (8:ℝ) > 0 := by linarith
              have h_2 : (l:ℝ) > 0 := by norm_cast
              have := div_pos h_1 h_2
              linarith
            norm_cast at this
          have : (l:ℝ) * m = 8 := by
            rw [← hm]
            apply mul_div_cancel₀
            norm_cast
            linarith
          norm_cast at this
          -- Step 8: Use divisors of 8 to find possible values of \(l\) and \(m\).
          have : ∃ l':ℕ, l' = l := by
             apply CanLift.prf
             linarith
          rcases this with ⟨l',hl'⟩
          have : ∃ m':ℕ, m' = m := by
            exact CanLift.prf m hmpos
          rcases this with ⟨m',hm'⟩
          have heq : l' * m' = 8 := by
            have : (l':ℤ) * (m':ℤ) = 8 := by
              rw [hl', hm', this]
            norm_cast at this
          have : l' ∣ 8 := by
            rw [← heq]
            exact Nat.dvd_mul_right l' m'
          have hdiv : Nat.divisors 8 = {1, 2, 4, 8} := by rfl
          have : l' ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨this, (by norm_num)⟩
          rw [hdiv] at this
          simp at this
          -- Step 9: For each divisor, calculate \(n\) and check if it satisfies the condition.
          rcases this with h1 | h2 | h3 | h4
          · rw [← hl', h1] at hneq
            norm_num at hneq
            norm_cast at hneq
            rw [hneq]
            simp
          · rw [← hl', h2] at hneq
            norm_num at hneq
            norm_cast at hneq
            rw [hneq]
            simp
          · rw [← hl', h3] at hneq
            norm_num at hneq
            norm_cast at hneq
            rw [hneq]
            simp
          · rw [← hl', h4] at hneq
            norm_num at hneq
            norm_cast at hneq
            rw [hneq]
            simp
        -- Step 10: Prove the reverse, that each calculated \(n\) is in the set \(s\).
        · intro hn
          have : n ∈ (s : Set ℕ) := by
            rw [hs]
            simp
            simp at hn
            rcases hn with h1 | h2 | h3 | h4
            · constructor
              · linarith
              · rw [h1]
                use 9
                field_simp
                norm_num
            · constructor
              · linarith
              · rw [h2]
                use 6
                field_simp
                norm_num
                have : √4 = 2 := by
                  apply Real.sqrt_eq_cases.mpr
                  left
                  exact ⟨(by norm_num), (by linarith)⟩
                rw [this]
                norm_num
            · constructor
              · linarith
              · rw [h3]
                use 6
                field_simp
                norm_num
                have : √16 = 4 := by
                  apply Real.sqrt_eq_cases.mpr
                  left
                  exact ⟨(by norm_num), (by linarith)⟩
                rw [this]
                norm_num
            · constructor
              · linarith
              · rw [h4]
                use 9
                field_simp
                norm_num
                have : √64 = 8 := by
                  apply Real.sqrt_eq_cases.mpr
                  left
                  exact ⟨(by norm_num), (by linarith)⟩
                rw [this]
                norm_num
          norm_cast
      -- Step 11: Sum the elements of the set to get the final result.
      rw [h]
      simp
