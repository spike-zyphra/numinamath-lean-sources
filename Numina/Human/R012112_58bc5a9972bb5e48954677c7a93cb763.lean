import Mathlib

/- Trouver tous les couples d'entiers naturels non nuls $(k, n)$ pour lesquels

$$
1!+2!+\cdots+k!=1+2+\cdots+n
$$ -/
theorem number_theory_605468 : {(k, n) : ℕ×ℕ | 0 < k ∧ 0 < n ∧ ∑ i in Finset.Icc 1 k, Nat.factorial i = ∑ i in Finset.Icc 1 n, i } = {(1, 1), (2, 2), (5, 17)} := by
  ext ⟨k, n⟩; simp only [Set.mem_setOf_eq, Prod.mk_one_one, Set.mem_insert_iff, Prod.mk_eq_one, Prod.mk.injEq, Set.mem_singleton_iff, iff_comm]
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    all_goals native_decide
  · rintro ⟨hk1, hn1, hsum⟩
    obtain ⟨A, hA⟩ := show ∃A : ℕ→ℕ, ∀n ≥ 1, A n = ∑ i in Finset.Icc 1 n, Nat.factorial i from ⟨λn ↦ ∑ i in Finset.Icc 1 n, Nat.factorial i, by simp⟩
    obtain ⟨B, hB⟩ := show ∃B : ℕ→ℕ, ∀n ≥ 1, B n = ∑ i in Finset.Icc 1 n, i from ⟨λn ↦ ∑ i in Finset.Icc 1 n, i, by simp⟩
    have hB' : ∀n ≥ 1, B n = n * (n + 1) / 2 := by
      intro n hn
      have : ∑ i ∈ Finset.Icc 1 n, i = ∑ i ∈ Finset.range (n + 1), i := by
        have : Finset.range (n + 1) = insert 0 (Finset.Icc 1 n) := by
          ext x
          simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
          omega
        rw [this, Finset.sum_insert, zero_add]
        simp
      rw [hB, this, Finset.sum_range_id, Nat.add_sub_self_right, mul_comm]
      exact hn
    rw [←hA _ (by omega), ←hB _ (by omega)] at hsum
    have hleft : n^2 < 2 * A k := by
      have : 2 * (n * (n + 1) / 2) = n * (n + 1) := by
        apply Nat.two_mul_div_two_of_even
        exact Nat.even_mul_succ_self n
      rw [hsum, hB' _ hn1, this]
      linarith
    have hright : 2 * A k < (n + 1)^2 := by
      have : 2 * (n * (n + 1) / 2) = n * (n + 1) := by
        apply Nat.two_mul_div_two_of_even
        exact Nat.even_mul_succ_self n
      rw [hsum, hB' _ hn1, this]
      linarith

    by_cases hk6 : k ≥ 6
    · have hmod₁ : A k ≡ 5 [MOD 7] := by
        have : A 6 ≡ 5 [MOD 7] := by
          have : A 6 = 873 := by rw [hA _ (by linarith)]; native_decide
          rw [this]
          native_decide
        apply Nat.ModEq.trans _ this
        have : Finset.Icc 1 k = Finset.Icc 1 6 ∪ Finset.Icc 7 k := by
          ext x; simp only [Finset.mem_Icc, Finset.mem_union]
          omega
        have hdisjoint : Disjoint (Finset.Icc 1 6) (Finset.Icc 7 k) := by
          rw [@Finset.disjoint_left]
          simp only [Finset.mem_Icc, not_and, not_le, and_imp]
          omega
        have h₁ : A k - A 6 = ∑ i ∈ Finset.Icc 7 k, Nat.factorial i := by
          rw [hA, hA, this, Finset.sum_union hdisjoint]
          all_goals omega
        rw [Nat.ModEq.comm, Nat.modEq_iff_dvd', h₁]
        apply Finset.dvd_sum
        simp only [Finset.mem_Icc, and_imp]
        intro i hi₁ hi₂
        apply Nat.dvd_factorial (by linarith) hi₁
        rw [hA, hA, this, Finset.sum_union hdisjoint]
        all_goals omega
      have hmod₂ : ∀ p > 0, ¬B p ≡ 5 [MOD 7] := by
        intro n hn' hn
        rw [hB' _ (by omega)] at hn
        have hn' : n * (n + 1) ≡ 3 [MOD 7] := by
          have : 2 * (n * (n + 1) / 2) = n * (n + 1) := by
            apply Nat.two_mul_div_two_of_even
            exact Nat.even_mul_succ_self n
          rw [this.symm]
          apply Nat.ModEq.trans (Nat.ModEq.mul rfl hn)
          native_decide
        rw [Nat.ModEq] at hn'
        obtain ⟨k, r, hk, hr⟩ := show ∃k r, n = 7 * k + r ∧ r < 7 by
          use n / 7, n % 7
          omega
        rw [hk, Nat.mul_mod, show (7 * k + r) % 7 = r by omega] at hn'
        rw [show (7 * k + r + 1) % 7 = (r + 1) % 7 by omega] at hn'
        interval_cases r <;> norm_num at hn'
      rw [hsum] at hmod₁
      specialize hmod₂ n hn1
      contradiction
    push_neg at hk6
    have hsum' : 2 * A k = n * (n + 1) := by
      rw [hsum, hB' _ hn1]
      apply Nat.two_mul_div_two_of_even
      exact Nat.even_mul_succ_self n
    interval_cases k
    · -- k = 1
      simp only [true_and, OfNat.one_ne_ofNat, false_and, or_self, or_false]
      have hA₁ : A 1 = 1 := by rw [hA _ (by linarith)]; native_decide
      rw [hA₁] at hleft hright
      have : n < 2 := by
        simp at hleft
        rw [←Nat.pow_lt_pow_iff_left]
        apply lt_trans hleft
        all_goals linarith
      by_contra!
      have : n = 0 := by omega
      rw [this] at hright
      norm_num at hright
    · -- k = 2
      simp only [OfNat.ofNat_ne_one, false_and, true_and, Nat.reduceEqDiff, or_false, false_or]
      have hA₂ : A 2 = 3 := by rw [hA _ (by linarith)]; native_decide
      rw [hA₂] at hleft hright
      have : n < 3 := by
        simp at hleft
        rw [←Nat.pow_lt_pow_iff_left]
        apply lt_trans hleft
        all_goals linarith
      by_contra!
      simp [show n = 1 by omega] at hright
    · -- k = 3
      simp only [OfNat.ofNat_ne_one, false_and, Nat.succ_ne_self, Nat.reduceEqDiff, or_self]
      have hA₃ : A 3 = 9 := by rw [hA _ (by linarith)]; native_decide
      rw [hA₃] at hsum' hleft
      norm_num at hsum' hleft
      have : n < 5 := by
        rw [←Nat.pow_lt_pow_iff_left]
        apply lt_trans hleft
        all_goals linarith
      interval_cases n <;> norm_num at hsum'
    · -- k = 4
      simp only [OfNat.ofNat_ne_one, false_and, Nat.succ_ne_self, Nat.reduceEqDiff, or_self]
      have hA₄ : A 4 = 33 := by rw [hA _ (by linarith)]; native_decide
      rw [hA₄] at hsum' hleft
      norm_num at hsum' hleft
      have : n < 9 := by
        rw [←Nat.pow_lt_pow_iff_left]
        apply lt_trans hleft
        all_goals linarith
      interval_cases n <;> norm_num at hsum'
    · -- k = 5
      simp only [OfNat.ofNat_ne_one, false_and, Nat.reduceEqDiff, true_and, false_or]
      have hA₅ : A 5 = 153 := by rw [hA _ (by linarith)]; native_decide
      rw [hA₅] at hsum' hleft
      norm_num at hsum' hleft
      have : n < 18 := by
        rw [←Nat.pow_lt_pow_iff_left]
        apply lt_trans hleft
        all_goals linarith
      interval_cases n <;> norm_num at hsum'
      rfl
