import Mathlib

/- theorem from latest mathlib, named `Nat.pow_right_inj`.  -/
lemma l_nat_pow_right_inj {a m n: ℕ} (ha : 1 < a) : a ^ m = a ^ n ↔ m = n := by
  simp [Nat.le_antisymm_iff, Nat.pow_le_pow_iff_right ha]

/- theorem from latest mathlib, named `Nat.pow_eq_one`. -/
lemma l_pow_eq_one {a n: ℕ} : a ^ n = 1 ↔ a = 1 ∨ n = 0 := by
  obtain rfl | hn := Decidable.em (n = 0)
  · simp
  · have h1: 0 ≤ a := by simp
    have h2: 0 ≤ 1 := by simp
    simpa [hn] using (pow_left_inj₀ h1 h2 hn) 

/- Example 15 (Problem from the 29th Russian Mathematical Olympiad) Find all prime numbers $p$ such that $p^{x}=y^{3}+1$ holds, where $x, y$ are positive integers. -/
theorem number_theory_150655 {p: ℕ} (pp: Nat.Prime p):
  (∃ x > 0, ∃ y > 0, p^x = y^3+1) ↔ (p = 2 ∨ p = 3) := by

  constructor

  · rintro ⟨x, xpos, y, ypos, heq⟩
    -- y^3+1 = (y+1)(y^2-y+1)
    have h1: y^3+1 = (y+1) * (y^2-y+1) := by
      zify
      rw [Nat.cast_sub (Nat.le_self_pow (by norm_num) y)]
      push_cast
      ring
    -- y+1 divide y^3+1 divide p^x, so it's p-power.
    obtain ⟨t, tlex, h2⟩: ∃ t, t ≤ x ∧ y+1 = p^t := by
      have: y+1 ∣ y^3 + 1 := by
        rw [h1]
        apply Nat.dvd_mul_right
      rwa [← heq, Nat.dvd_prime_pow pp] at this
    -- therefore y^2-y+1 = p^(x-t)
    have h3: y^2-y+1 = p^(x-t) := by
      rw [h2, ← heq, show x = x-t + t by simp [tlex],
      add_comm _ t, pow_add] at h1
      simp only [mul_eq_mul_left_iff, Nat.pow_eq_zero,
      pp.ne_zero, ne_eq, false_and, or_false] at h1
      rw [h1]
    -- y+1 = p^t, y = p^t - 1
    replace h2: y = p^t - 1 := by simp [← h2]
    -- substitute it into equation y^2-y+1 = p^(x-t)
    replace h3: p^(t*2) - 3*p^t + (3:ℤ) = p^(x-t) := by
      zify at h3
      rw [Nat.cast_sub (Nat.le_self_pow (by norm_num) y)] at h3
      rw [h2] at h3
      push_cast at h3
      rw [Nat.cast_sub (Nat.one_le_pow t p pp.pos)] at h3
      push_cast at h3
      rw [← h3]
      ring
    replace h3: (3:ℤ) * (p^t - 1) = p^(t*2) - p^(x-t) := by
      linarith only [h3]
    replace h3: (3:ℤ) * (p^t - 1) = p^(x-t) * (p^(3*t-x) - 1) := by
      have: x-t < t*2 := by
        by_contra! hh1
        replace hh1: p^(t*2) ≤ p^(x-t) :=
          Nat.pow_le_pow_right pp.pos hh1
        zify at hh1
        have hh2: (3:ℤ) * (p^t - 1) ≤ 0 := by
          rw [h3]
          exact Int.sub_nonpos_of_le hh1
        replace hh2: 3 * (p^t-1) ≤ 0 := by
          zify
          convert hh2
          simp [Nat.cast_sub (Nat.one_le_pow t p pp.pos)]
        simp only [nonpos_iff_eq_zero, mul_eq_zero,
        OfNat.ofNat_ne_zero, false_or] at hh2
        replace hh2: t = 0 := by
          suffices p^t = p^0 by
            rwa [l_nat_pow_right_inj pp.one_lt] at this
          rw [Nat.pow_zero]
          omega
        simp only [hh2, pow_zero, sub_self, mul_zero,
        zero_mul, tsub_zero] at h3
        replace h3: p^x = (1:ℤ) := by linarith only [h3]
        norm_cast at h3
        simp [l_pow_eq_one, xpos.ne', pp.ne_one] at h3
      rw [show t*2 = t*2 - (x-t) + (x-t) by simp [this.le],
      add_comm _ (x-t), pow_add, ← mul_sub_one] at h3
      convert h3 using 4
      omega
    -- then 3 divide p^(x-t) or p^(3t-x) - 1
    have h4: 3 ∣ 3 * (p^t - 1: ℤ) := by
      apply Int.dvd_mul_right
    have: (p:ℤ)^(3*t-x) - 1 = ↑(p^(3*t-x) - 1: ℕ) := by
      simp [Nat.cast_sub (Nat.one_le_pow _ _ pp.pos)]
    rw [h3, this] at h4
    norm_cast at h4
    rw [Nat.Prime.dvd_mul (by norm_num)] at h4
    rcases h4 with h4 | h4
    · -- 3 divide p^(x-t), we solve p = 3
      replace := Nat.Prime.dvd_of_dvd_pow (by norm_num) h4
      rw [pp.dvd_iff_eq (by norm_num)] at this
      simp [this]
    · -- otherwise, p^(x-t) divide p^t - 1
      replace h4: p^(x-t) ∣ p^t - 1 := by
        rcases h4 with ⟨k, hk⟩
        rw [this, hk] at h3
        use k
        replace: p^t - (1:ℤ) = ↑(p^t-1: ℕ) := by
          rw [Nat.cast_sub (Nat.one_le_pow _ _ pp.pos)]
          simp
        rw [this] at h3
        norm_cast at h3
        linarith only [h3]
      -- then x-t = 0
      have h5: x - t = 0 := by
        by_contra!
        replace: p ∣ p^t - 1 := by
          apply Dvd.dvd.trans ?_ h4
          exact dvd_pow_self p this
        have hh: p^t - 1 = (p^t-1)/(p-1) * (p-1) := by
          refine Eq.symm (Nat.div_mul_cancel ?_)
          nth_rw 2 [show 1 = 1^t by simp]
          apply nat_sub_dvd_pow_sub_pow
        rw [hh, ← Nat.geomSum_eq pp.two_le, pp.dvd_mul] at this
        rcases this with h5 | h5
        · by_cases ht: t = 0
          · simp [h2, ht] at ypos
          · replace ht: 0 < t := Nat.zero_lt_of_ne_zero ht
            rw [show t = t-1+1 by simp [Nat.sub_add_cancel ht],
            Finset.sum_range_succ'] at h5
            have h6: p ∣ ∑ k ∈ Finset.range (t-1), p^(k+1) := by
              apply Finset.dvd_sum (fun i _ => ?_)
              use p^i; ring
            replace h6: p ∣ p^0 := by
              exact (Nat.dvd_add_iff_right h6).mpr h5
            simp only [pow_zero, Nat.dvd_one] at h6
            norm_num [h6] at pp
        · replace: 0 < p - 1 :=
            Nat.zero_lt_sub_of_lt pp.one_lt
          replace := Nat.le_of_dvd this h5
          absurd this
          push_neg
          exact Nat.sub_one_lt pp.ne_zero
      replace h5: x = t := by
        refine Nat.le_antisymm ?_ tlex
        exact Nat.le_of_sub_eq_zero h5
      -- then 3(p^t-1) = p^t^2 - 1, p^t+1 = 3, we solve p^t = 2
      replace h3: p^t = 2 := by
        rw [this, h5, show 3*t-t = t*2 by omega] at h3
        simp only [tsub_self, pow_zero, one_mul] at h3
        replace: p^t - (1:ℤ) = ↑ (p^t-1: ℕ) := by
          simp [Nat.cast_sub (Nat.one_le_pow _ _ pp.pos)]
        rw [show 1 = 1^2 by simp, this,
        Nat.pow_mul, Nat.sq_sub_sq] at h3
        norm_cast at h3
        simp only [mul_eq_mul_right_iff, Nat.reduceEqDiff] at h3
        refine h3.resolve_right ?_
        suffices 1 < p^t by
          exact Nat.sub_ne_zero_iff_lt.mpr this
        apply Nat.one_lt_pow ?_ pp.one_lt
        simp [← h5, xpos.ne']
      -- this case we find p = 2
      left
      apply le_antisymm ?_ pp.two_le
      rw [← h3, ← h5]
      exact Nat.le_self_pow xpos.ne' p

  -- verification
  rintro (rfl | rfl)
  · exact ⟨1, (by norm_num), 1, (by norm_num), (by norm_num)⟩
  · exact ⟨2, (by norm_num), 2, (by norm_num), (by norm_num)⟩