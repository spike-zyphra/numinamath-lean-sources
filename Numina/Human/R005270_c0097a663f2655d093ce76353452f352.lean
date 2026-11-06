import Mathlib

/- Trouver tous les couples de nombres premiers ( $p, q$ ) tels que :
$$
\mathrm{p}^{2}\left(\mathrm{p}^{3}-1\right)=\mathrm{q}(\mathrm{q}+1)
$$ -/
theorem number_theory_607288{p q: ℕ}
  (pp: Nat.Prime p)(pq: Nat.Prime q):
  p^2 * (p^3 - 1) ≠ q * (q+1) := by
  -- suppose on the contrary, this equation holds.
  by_contra! h
  -- first, we consider p=q case
  by_cases hpq: p = q
  · -- if p=q, we have p^4-p = p+1, or, p^4 = 2p+1
    have h1: p^4 = 2*p + 1 := by
      simp [← hpq, pow_two, mul_assoc p _ _,
      pp.ne_zero] at h
      rw [p.mul_sub, ← pow_succ'] at h
      simp at h
      omega
    -- but p^4 > 2p+1 given p ≥ 2
    have h2{n:ℕ}(hn: n ≥ 2): n^4 > 2*n + 1 := by
      by_cases hhn: n = 2
      · simp [hhn]
      replace hn: n ≥ 3 := by omega
      have hh1: n^2 > 2*n + 1 := by
        zify
        apply lt_of_sub_pos
        have: (n^2:ℤ) - (2*n+1) = (n-1)^2 - 2 := by ring
        rw [this]; apply sub_pos_of_lt
        zify at hn
        replace: (n-1:ℤ)^2 ≥ 2^2 := by
          apply (pow_le_pow_iff_left₀ (by norm_num)
            (by linarith [hhn]) (by norm_num)).mpr (by linarith [hn])
        simp at this; linarith [this]
      apply lt_trans hh1 ?_
      nlinarith [hn]
    -- contradiction
    have h2': p^4 > 2*p + 1 := by
      apply h2
      exact Nat.Prime.two_le pp
    simp [h1] at h2'
  · -- now p ≠ q
    -- this case we have p^2 ∣ q+1
    have h1: p^2 ∣ q+1 := by
      have: p^2 ∣ q*(q+1) := by
        rw [← h]
        exact Nat.dvd_mul_right _ _
      -- p^2 coprime to q, so p^2 ∣ q+1
      apply Nat.Coprime.dvd_of_dvd_mul_left ?_ this
      apply Nat.Coprime.pow_left 2 ?_
      exact (Nat.coprime_primes pp pq).mpr hpq
    -- q coprime to p^2, q ∣ p^3-1
    have h2: q ∣ (p-1)*(p^2+p+1) := by
      have: q ∣ p^2 * (p^3-1) := by
        rw [h]
        exact Nat.dvd_mul_right _ _
      rcases ((Nat.Prime.dvd_mul pq).mp this) with hh1 | hh2
      · -- p≠q, impossible for q ∣ p^2
        absurd hh1
        refine (Nat.Prime.coprime_iff_not_dvd pq).mp ?_
        refine Nat.Coprime.pow_right 2 ?_
        apply (Nat.coprime_primes pq pp).mpr fun a => hpq (id (Eq.symm a))
      · -- p^3-1 = (p-1)(p^2+p+1)
        zify at hh2
        have: 1 ≤ p^3 := one_le_pow₀ pp.one_le
        rw [Nat.cast_sub this] at hh2
        push_cast at hh2; rw [← geom_sum_mul] at hh2
        simp [Finset.sum_range_succ] at hh2
        zify; rw [Nat.cast_sub pp.one_le]
        ring_nf at hh2; ring_nf; exact hh2
    rcases ((Nat.Prime.dvd_mul pq).mp h2) with h21 | h22
    · -- if q ∣ p-1, then q ≤ p-1, or q+1 = ≤ p
      have hh1: q+1 ≤ p := by
        have: 0 < p-1 := by
          have: 2 ≤ p := pp.two_le
          omega
        replace: q ≤ p-1 := Nat.le_of_dvd this h21
        omega
      -- p^2 ∣ q+1, p^2 ≤ q+1
      have hh2: p^2 ≤ q+1 := Nat.le_of_dvd (by simp) h1
      have hh3: p^2 ≤ p := le_trans hh2 hh1
      -- therefore we obtain p^2 ≤ p, or p ≤ 1
      replace hh3: p ≤ 1 := by
        nth_rw 2 [← one_mul p] at hh3; rw [pow_two] at hh3
        nlinarith [hh3]
      -- contradiction
      linarith [pp.two_le, hh3]
    · -- q ∣ p^2+p+1
      -- then q ≤ p^2+p+1, or, q+1 ≤ p^2+p+2
      have hh: q+1 ≤ p^2+p+2 := by
        have: q ≤ p^2+p+1 := Nat.le_of_dvd (by simp) h22
        linarith [this]
      -- p ≥ 2, so p+2 ≤ p^2. moreover, we can find p ≠ 2, and p+2 < p^2
      -- first, we prove p cannot be 2, or, p > 2.
      have pgt2: p > 2 := by
        apply lt_of_le_of_ne pp.two_le ?_
        by_contra! hp
        simp [← hp] at h
        -- no answer for q(q+1) = 28.
        have hq1: q < 5 := by
          by_contra!
          have: q*(q+1) ≥ 30 := by nlinarith [this]
          simp [← h] at this
        have hq2: 4 < q := by
          by_contra!
          have: q*(q+1) ≤ 20 := by nlinarith [this]
          simp [← h] at this
        omega
      -- therefore q+1 < 2p^2
      replace hh: q+1 < 2*p^2 := by
        -- p > 2, so p+2 < p^2
        have: p+2 < p^2 := calc
          p+2 < p+p := by linarith [pgt2]
          _ = 2*p := by ring
          _ < p*p := Nat.mul_lt_mul_of_pos_right pgt2 pp.pos
          _ = p^2 := by ring
        replace: p^2+p+2 < 2*p^2 := by
          rw [two_mul, add_assoc]
          linarith [this]
        apply lt_of_le_of_lt hh this
      -- but p^2 ∣ q+1, suppose kp^2 = q+1
      rcases h1 with ⟨k, hk⟩
      rw [hk, mul_comm _ k] at hh
      -- kp^2 < 2p^2, k < 2.
      replace hh: k < 2 := by
        have: 0 < p^2 := pow_pos pp.pos _
        exact (Nat.mul_lt_mul_right this).mp hh
      -- but k cannot be 0 or 1, contradiction
      have kne0: k ≠ 0 := by
        by_contra!
        simp [this] at hk
      have kne1: k ≠ 1 := by
        by_contra!
        simp [this] at hk
        -- q+1 = p^2, then q = p^2-1
        -- and p^2-1 ∣ p^2-1 + (p+2), we have p^2-1 ∣ p+2
        replace hh: p^2-1 ∣ p+2 := by
          have hh1: p^2-1 = q := by omega
          have hh2: p^2+p+1 = (p^2-1) + (p+2) := by
            have: 1 ≤ p^2 := by
              apply one_le_pow₀ pp.one_le
            omega
          rw [← hh1, hh2] at h22
          exact Nat.dvd_add_self_left.mp h22
        -- then p^2 - 1 ≤ p+2, or p^2 ≤ p+3, contradiction with p < 2
        replace hh: p^2 ≤ p+3 := by
          have: p^2-1 ≤ p+2 := Nat.le_of_dvd (by simp) hh
          omega
        have not_hh: p^2 > p+3 := calc
          p^2 = p*p := by ring
          _ > p*2 := by
            apply Nat.mul_lt_mul_of_pos_left pgt2 pp.pos
          _ = p+p := by ring
          _ ≥ p+3 := by omega
        linarith [hh, not_hh]
      -- k<2 but k ≠ 0 and ≠ 1, contradiction.
      omega