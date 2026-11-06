import Mathlib

/- Find all positive integers $n$ for which there is a positive integer $k$ so that
for every positive divisor $d$ of $n$，$d-k$ is also a (not necessarily positive) divisor of $n$. -/

theorem number_theory_606273: {n: ℤ | 0 < n ∧ (∃ k, 0 < k ∧ ∀ d: ℤ, (0 < d ∧ d ∣ n) → (d - k)∣ n)}
    = {n: ℤ | 0 < n ∧ (n ≤ 6 ∨ Prime n)} := by

    ext n
    constructor

    -- the forward direction
    .
      intro h
      simp only [Set.mem_setOf_eq] at h
      simp
      rcases h with ⟨hn, h⟩
      obtain ⟨k, hk, h⟩ := h
      simp [hn]
      by_cases ln: n ≤ 6
      .
        simp [ln]
      --case n > 6
      .
        simp at ln
        right

        -- we show n / 2 ≤ k
        have l1: (n: ℚ) / 2 ≤ k := by
          specialize h n
          simp [hn] at h
          apply exists_eq_mul_right_of_dvd at h
          obtain ⟨m, hm⟩ := h
          by_contra! o
          have o1: 0 ≤ n - k := by
            qify
            qify at hn
            nlinarith
          have o2: 1 < m := by nlinarith
          replace o2: 2 ≤ m := by omega
          qify at o2 o1
          qify at hm
          absurd o
          simp
          nlinarith

        -- we then have 1 - k < - 3 / n
        have l: 1 - k < - (n: ℚ) / 3 := by
          replace l1: 1 - ↑k ≤ 1 - (n: ℚ) / 2 := by linarith
          have i: 1 - (n: ℚ) / 2 < - (n: ℚ) / 3 := by
            field_simp
            qify at ln
            linarith
          linarith

        -- combine the two inequalities, we have 1 - k = -n or -n / 2
        have r: 1 - k = - (n: ℚ) ∨ 1 - k = - (n: ℚ) / 2 := by
          clear l1
          specialize h 1
          norm_num at h
          apply exists_eq_mul_right_of_dvd at h
          obtain ⟨m, hm⟩ := h
          have o: m < 0 := by nlinarith
          have lm: -3 < m := by
            by_contra! s
            qify at hm
            absurd l
            simp
            rw [hm]
            qify at s
            replace hk: 1 ≤ k := by omega
            qify at hk
            nlinarith
          have t: m = -1 ∨ m = -2 := by omega
          rcases t with t | t
          .
            simp [t] at hm
            left
            qify at hm
            linarith
          .
            simp [t] at hm
            right
            qify at hm
            linarith

        rcases r with r | r
        -- case k = n + 1
        .
          norm_cast at r
          clear l1 l
          replace r: k = n + 1 := by omega
          by_contra! pp

          -- then there's a nontrivial divisor of n
          have hd: ∃ d, 1 < d ∧ d < n ∧  d ∣ n := by
            let n':= n.natAbs
            have qq: ¬ Nat.Prime n' := by
              simp [n']
              rw [← Int.prime_iff_natAbs_prime]
              exact pp
            apply Nat.exists_dvd_of_not_prime at qq
            obtain ⟨d', i, j, s⟩ := qq
            use d'
            have od': 1 < d' := by
              have o: d' ≠ 0 := by
                by_contra! o
                simp [o] at i
                simp [n'] at i
                simp [i] at hn
              omega
            have sd': d' < n := by
              apply Nat.le_of_dvd at i
              zify at i s
              simp [n'] at i s
              rw [show |n| = n by apply abs_of_nonneg; omega] at i s
              omega
              simp [n']
              omega
            simp [od', sd']
            zify at i
            simp [n'] at i
            exact i
            simp [n']
            omega

          obtain ⟨d, hd1,hd2, dd⟩ := hd
          specialize h d
          have x: 0 < d := by omega
          simp [x, dd] at h
          clear x
          rw [r] at h
          replace h: d - (n + 1) ∣ d - 1 := by
            rw [show d - 1 = d - (n + 1) + n by ring]
            apply dvd_add
            simp
            exact h
          rw [← Int.neg_dvd] at h
          rw [show - (d - (n + 1)) = n + 1 - d by ring] at h
          apply exists_eq_mul_right_of_dvd at h
          obtain ⟨m, hm⟩ := h
          have lm: 0 < m := by nlinarith
          replace lm: 1 ≤ m := by omega
          have l: n + 2 ≤ 2 * d := by nlinarith
          apply exists_eq_mul_right_of_dvd at dd
          obtain ⟨v, hv⟩ := dd
          have ov: 0 < v := by nlinarith
          replace ov: 1 ≤ v := by omega
          rw [hv] at l
          have iv: v ≠ 1 := by
            by_contra! g
            simp [g] at hv
            simp [hv] at hd2
          have ov: 2 ≤ v := by omega
          nlinarith

        -- case k = n / 2 + 1
        .
          clear l l1
          replace r: n - k = (n: ℚ) / 2 - 1 := by nlinarith
          specialize h n
          simp [hn] at h
          apply exists_eq_mul_right_of_dvd at h
          obtain ⟨m, hm⟩ := h
          qify at hm
          rw [r] at hm
          replace hm: 2 * n = (n - (2: ℚ)) * m := by field_simp at hm; linarith
          norm_cast at hm
          have c: n - 2 ∣ 2 * n := by  -- this is where we find the contradiction
            rw [hm]
            simp
          replace c: n - 2 ∣ 4 := by
            rw [show 4 = 2 * n - 2 * (n - 2) by ring]
            apply dvd_sub
            exact c
            simp
          apply exists_eq_mul_right_of_dvd at c
          obtain ⟨v, hv⟩ := c
          have ov: 0 < v := by nlinarith
          replace ov: 1 ≤ v := by omega
          nlinarith


    -- the backward direction
    .
      intro h
      simp only [Set.mem_setOf_eq] at h
      simp only [Set.mem_setOf_eq]
      rcases h with ⟨hn, h⟩
      simp [hn]
      rcases h with h | h
      -- case n ≤ 6
      .
        interval_cases n
        . -- n = 1
          use 2
          simp
          intro d hd
          intro l
          apply exists_eq_mul_right_of_dvd at l
          obtain ⟨m, hm⟩ := l
          have o: 0 < m := by nlinarith
          replace o: 1 ≤ m := by omega
          have s: d = 1 := by nlinarith
          simp [s]
        . -- n = 2
          use 3
          simp
          intro d hd
          intro l
          apply exists_eq_mul_right_of_dvd at l
          obtain ⟨m, hm⟩ := l
          have o: 0 < m := by nlinarith
          replace o: 1 ≤ m := by omega
          have s: d ≤ 2:= by nlinarith
          interval_cases d
          all_goals norm_num
        . -- n = 3
          use 4
          simp
          intro d hd
          intro l
          apply exists_eq_mul_right_of_dvd at l
          obtain ⟨m, hm⟩ := l
          have o: 0 < m := by nlinarith
          replace o: 1 ≤ m := by omega
          have s: d ≤ 3:= by nlinarith
          interval_cases d
          all_goals try norm_num
          have o: (2: ℤ)∣ 3 := by
            rw [hm]
            simp
          norm_num at o
        . -- n = 4
          use 3
          norm_num
          intro d hd
          intro l
          apply exists_eq_mul_right_of_dvd at l
          obtain ⟨m, hm⟩ := l
          have o: 0 < m := by nlinarith
          replace o: 1 ≤ m := by omega
          have s: d ≤ 4:= by nlinarith
          interval_cases d
          all_goals try norm_num
          have o: (3: ℤ)∣ 4 := by
            rw [hm]
            simp
          norm_num at o
        . -- n = 5
          use 6
          norm_num
          intro d hd
          intro l
          apply exists_eq_mul_right_of_dvd at l
          obtain ⟨m, hm⟩ := l
          have o: 0 < m := by nlinarith
          replace o: 1 ≤ m := by omega
          have s: d ≤ 5:= by nlinarith
          interval_cases d
          all_goals try norm_num
          .
            have o: (2: ℤ)∣ 5 := by
              rw [hm]
              simp
            norm_num at o
          .
            have o: (3: ℤ)∣ 5 := by
              rw [hm]
              simp
            norm_num at o
          .
            have o: (4: ℤ)∣ 5 := by
              rw [hm]
              simp
            norm_num at o
        . -- n = 6
          use 4
          norm_num
          intro d hd
          intro l
          apply exists_eq_mul_right_of_dvd at l
          obtain ⟨m, hm⟩ := l
          have o: 0 < m := by nlinarith
          replace o: 1 ≤ m := by omega
          have s: d ≤ 6:= by nlinarith
          interval_cases d
          all_goals try norm_num
          have o: (4: ℤ)∣ 6 := by
            rw [hm]
            simp
          norm_num at o

      -- case n is prime
      .
        use (n + 1)
        constructor
        .
          omega
        .
          intro d hd l
          have o: d = 1 ∨ d = n := by
            by_contra! o
            rcases o with ⟨o1, o2⟩
            let d':= d.natAbs
            let n':= n.natAbs
            rw [← Int.natAbs_dvd_natAbs] at l
            rw [Nat.Prime.dvd_iff_eq] at l
            zify at l
            rw [show |n| = n by apply abs_of_nonneg; omega] at l
            rw [show |d| = d by apply abs_of_nonneg; omega] at l
            tauto
            rw [← Int.prime_iff_natAbs_prime]
            exact h
            omega
          rcases o with o | o
          .
            simp [o]
          .
            simp [o]