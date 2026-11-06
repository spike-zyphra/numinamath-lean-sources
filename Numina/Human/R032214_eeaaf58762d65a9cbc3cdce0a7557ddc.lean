import Mathlib.Tactic

def a : ℕ → ℤ
| 0 => 2
| n + 1 => (a n)^2 - a n + 1

/- 16th Putnam 1956 Problem B6
The sequence `a n` is defined by `a 0 = 2` and `a n+1 = a n^2 - a n + 1`.
We aim to prove two properties:
1. Any pair of values in the sequence are relatively prime.
2. The infinite sum of the reciprocals of the sequence equals 1: ∑ 1/a n = 1.
-/
theorem number_theory_122359 :
    (∀ m n, m ≠ n → IsCoprime (a m) (a n)) ∧ ∑' n, (1 : ℝ)/(a n) = 1 := by
      -- Define a helper function `f` to represent the reciprocal of `a n` as a real number.
      let f : ℕ → ℝ := fun i => (1:ℝ) / (a i)

      -- Step 1: Prove a lower bound for the sequence `a n`.
      -- Claim: `a n ≥ n` for all `n`.
      have hge : ∀ n, a n ≥ n := by
        intro n
        induction n with
        | zero =>
          -- Base case: `a 0 = 2`, and `2 ≥ 0`.
          unfold a
          norm_cast
        | succ n hn =>
          -- Inductive step: Assume `a n ≥ n`. We must show `a (n + 1) ≥ n + 1`.
          unfold a
          by_cases hnzero : n = 0
          · rw [hnzero]
            -- Special case: `n = 0`. By definition, `a 1 = 2`, and `2 ≥ 1`.
            unfold a
            simp
          · by_cases hnone : n = 1
            · rw [hnone]
              -- Special case: `n = 1`. By definition, `a 2 = 5`, and `5 ≥ 2`.
              unfold a
              unfold a
              simp
            · have : n ≥ 2 := by apply (Nat.two_le_iff n).mpr ⟨hnzero, hnone⟩
              -- General case: Use the inductive hypothesis and properties of the recurrence.
              have : n - 1 ≥ 1 := by exact Nat.le_sub_one_of_lt this
              calc
                _ = a n * (a n - 1) + 1 := by ring
                _ ≥ a n * (n - 1) + 1 := by nlinarith
                _ ≥ a n * 1 + 1 := by nlinarith
                _ ≥ n + 1 := by nlinarith
                _ ≥ _ := by norm_cast

      -- Step 2: Prove a modular property of the sequence.
      -- Claim: For all `n` and `k ≥ 1`, `a (n + k) % a n = 1`.
      have hmod : ∀ n, ∀ k ≥ 1, a (n + k) % (a n) = 1 := by
        intro n
        intro k
        induction k with
        | zero =>
          -- Base case: `k = 0`, which contradicts `k ≥ 1`.
          intro h
          linarith
        | succ k hk =>
          -- Inductive step: Assume the modular property holds for `k`. Prove it for `k + 1`.
          have : a (n + (k + 1)) = (a (n+k))^2 - a (n+k) + 1 := by rfl
          intro hk'
          rw [this]
          by_cases hkpos : k ≥ 1
          · calc
              _ = (a (n + k) ^ 2 % a n - a (n + k) % a n + 1 % a n) % a n := by
                rw [Int.add_emod, Int.sub_emod]
                simp
              _ = _ := by
                have := hk hkpos
                rw [pow_two, Int.mul_emod]
                rw [this]
                simp
                apply Int.emod_eq_of_lt (by linarith)
                by_cases hn : n = 0
                · rw [hn]
                  unfold a
                  linarith
                · by_cases hn' : n = 1
                  · rw [hn']
                    unfold a
                    unfold a
                    simp
                  · have : n ≥ 2 := by apply (Nat.two_le_iff n).mpr ⟨hn, hn'⟩
                    have := hge n
                    linarith
          · have : k = 0 := by exact Nat.eq_zero_of_not_pos hkpos
            rw [this]
            simp
            rw [Int.add_emod, Int.sub_emod]
            have : (a n) ^ 2 % a n = 0 := by
              apply Int.emod_eq_zero_of_dvd
              exact Dvd.intro_left ((a n).pow 1) rfl
            rw [this]
            simp
            apply Int.emod_eq_of_lt (by linarith)
            by_cases hn : n = 0
            · rw [hn]
              unfold a
              linarith
            · by_cases hn' : n = 1
              · rw [hn']
                unfold a
                unfold a
                simp
              · have : n ≥ 2 := by apply (Nat.two_le_iff n).mpr ⟨hn, hn'⟩
                have := hge n
                linarith

      -- Step 3: Prove the sum formula for partial sums of `1/a n`.
      -- Claim: For all `n`, the partial sum ∑ 1/a i from `i = 0` to `n` equals `1 - 1/(a (n+1) - 1)`.
      have hsum : ∀ n, ∑ i ∈ Finset.Icc 0 n, f i = 1 - 1 / (a (n+1) - 1) := by
        intro n
        induction n with
        | zero =>
          -- Base case: `n = 0`. The sum is `1/a 0 = 1/2`, which matches the formula.
          simp
          unfold f
          unfold a
          unfold a
          field_simp
          norm_num
        | succ n hn =>
          -- Inductive step: Assume the formula holds for `n`. Prove it for `n + 1`.
          calc
            _ = (∑ i ∈ Finset.Icc 0 n, f i) + f (n+1) := by
              apply Finset.sum_Icc_succ_top (by linarith) f
            _ = _ := by
              rw [hn]
              unfold f
              have : a (n + 1 + 1) = (a (n+1))^2 - a (n+1) + 1 := rfl
              rw [this]
              field_simp
              have : - (1:ℝ) / (↑(a (n + 1)) - 1) + 1 / ↑(a (n + 1)) = - 1 / (↑(a (n + 1)) ^ 2 - ↑(a (n + 1))) := by
                have : a (n + 1) > 1 := by
                  by_cases hzero : n = 0
                  · rw [hzero]
                    unfold a
                    unfold a
                    norm_num
                  · have := hge (n+1)
                    apply lt_of_lt_of_le ?h this
                    norm_cast
                    exact Nat.sub_ne_zero_iff_lt.mp hzero
                have h1 : - (1:ℝ) / (↑(a (n + 1)) - 1) = -1 * (a (n+1)) / ((↑(a (n + 1)) - 1) * (a (n+1))) := by
                  refine Eq.symm (mul_div_mul_right (-(1:ℝ)) (↑(a (n + 1)) - 1) ?hc)
                  norm_cast
                  linarith
                have h2 : (1:ℝ) / ↑(a (n + 1)) = (1 * (↑(a (n + 1)) - 1)) / ((↑(a (n + 1)) - 1) * (a (n+1))) := by
                  nth_rw 2 [mul_comm]
                  refine Eq.symm (mul_div_mul_right (1:ℝ) ↑(a (n + 1)) ?hc')
                  norm_cast
                  linarith
                simp at h1
                rw [h1, h2]
                rw [div_add_div_same]
                ring
              calc
                _ = (1:ℝ) + (- (1:ℝ) / (↑(a (n + 1)) - 1) + 1 / ↑(a (n + 1))) := by ring
                _ = _ := by
                  rw [this]
                  ring

      -- Step 4: Prove that any two terms in the sequence are relatively prime.
      constructor
      · intro m n hmn
        -- Without loss of generality, assume `m > n`. (The other case is symmetric.)
        by_cases hmn : m > n
        · have hge : m - n ≥ 1 := by
            exact Nat.le_sub_of_add_le' hmn
          have := hmod n (m-n) hge
          have heq : n + (m-n) = m := by
            refine Nat.add_sub_of_le ?h
            linarith
          rw [heq] at this
          -- `a m % a n = 1`, so `a m` and `a n` are coprime.
          have : a m = a m / a n * a n + 1 := by
            rw [← this]
            exact Eq.symm (Int.ediv_add_emod' (a m) (a n))
          rw [this]
          apply IsCoprime.mul_add_right_left isCoprime_one_left (a m / a n)
        -- Symmetric case: Assume `n > m`.
        · have : n > m := by
            by_contra hle
            simp at hle
            simp at hmn
            have : m = n := by exact Nat.le_antisymm hmn hle
            contradiction
          have hge : n - m ≥ 1 := by
            exact Nat.le_sub_of_add_le' this
          have := hmod m (n-m) hge
          have heq : m + (n-m) = n := by
            refine Nat.add_sub_of_le ?hh
            linarith
          rw [heq] at this
          have : a n = a n / a m * a m + 1 := by
            rw [← this]
            exact Eq.symm (Int.ediv_add_emod' (a n) (a m))
          rw [this]
          apply IsCoprime.symm (IsCoprime.mul_add_right_left isCoprime_one_left (a n / a m))

      -- Step 5: Prove the infinite sum of the reciprocals equals 1.
      · have hipos : ∀ i, f i ≥ 0 := by
          intro i
          unfold f
          have := hge i
          by_cases hipos : i > 0
          · simp
            linarith
          · simp
            have : i = 0 := by exact Nat.eq_zero_of_not_pos hipos
            rw [this]
            unfold a
            linarith
        have hsumle : ∀ n, ∑ i ∈ Finset.range n, f i ≤ 1 := by
          intro n
          by_cases hnpos : n ≥ 1
          · have : Finset.range n = Finset.Icc 0 (n-1) := by
              apply Nat.range_eq_Icc_zero_sub_one n (Nat.not_eq_zero_of_lt hnpos)
            rw[this]
            rw [hsum (n-1)]
            simp
            rw [Nat.sub_add_cancel hnpos]
            norm_cast
            have := (hge n)
            linarith
          · have : n = 0 := by exact Nat.eq_zero_of_not_pos hnpos
            rw [this]
            simp
        have hle : ∑' n, (1:ℝ)/ (a n) ≤ 1 := by
          have := @Real.tsum_le_of_sum_range_le f 1 hipos hsumle
          unfold f at this
          linarith
        have hsummable : Summable f := by
          apply @summable_of_sum_range_le f 1 hipos hsumle
        have hge : ∑' n, (1:ℝ)/ (a n) ≥ 1 := by
          by_contra
          have h : (∑' n, (1:ℝ)/ (a n)) < 1 := by linarith
          have : ∃ δ, (∑' n, (1:ℝ)/ (a n)) < δ ∧ δ < 1 := by
            have := @exists_rat_btwn ℝ _ _ (∑' n, (1:ℝ)/ (a n)) 1 h
            rcases this with ⟨δ, hle⟩
            use δ
          rcases this with ⟨δ, hle⟩
          let ε := 1 - δ
          have hpos : ε > 0 := by unfold ε; linarith
          have : ∃ (N :ℕ), N > 1 / ε := by
            exact exists_nat_gt (1 / ε)
          rcases this with ⟨N, hN⟩
          have : ∀ i ∉ Finset.Icc 0 N, f i ≥ 0 := by
            intro i hi
            exact hipos i
          have := @sum_le_tsum ℕ ℝ _ _ _ f (Finset.Icc 0 N) this hsummable
          rw [hsum] at this
          have hlede : 1 - 1 / (↑(a (N + 1)) - 1) < δ := by linarith
          have hep : (a (N + 1):ℝ) - 1 > 1 / ε := by
            calc
              _ ≥ ((N + 1):ℝ) - 1 := by
                have := hge (N+1)
                norm_cast at this
                have : ((a (N + 1)):ℝ) ≥ (((N+1):ℤ):ℝ) := by norm_cast
                calc
                  _ ≥ (((N+1):ℤ):ℝ) - 1 := by linarith
                  _ = _ := by norm_cast
              _ > _ := by
                ring_nf
                have : 1 / ε = (1 - δ)⁻¹ := by
                  unfold ε
                  ring_nf
                rw [this] at hN
                linarith
          have hfrac : 1 / (↑(a (N + 1)) - 1) < ε := by
            have : 1 / ε > 0 := by exact one_div_pos.mpr hpos
            have := one_div_lt_one_div_of_lt this hep
            simp at this
            simp
            exact this
          have hgede :  1 - 1 / (↑(a (N + 1)) - 1) > δ := by
            calc
              _ > 1 - ε := by apply sub_lt_sub_left hfrac
              _ = _ := by unfold ε; ring
          linarith
        linarith
