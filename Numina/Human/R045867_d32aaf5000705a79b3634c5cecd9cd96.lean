import Mathlib

/- 1.2. For each positive integer $k$, prove that there is a perfect square of the form $n 2^{k}-7$,
where $n$ is a positive integer. -/

theorem number_theory_228385 (k : ℕ) (hk : k > 0) :
    ∃ n: ℤ, IsSquare (n * 2 ^ k - 7) ∧ n > 0 := by

    -- we prove by induction
    induction' k with k ih
    .
        norm_num at hk
    .
        -- we first prove the case k = 0, 1, 2
        by_cases lk: k = 0
        .
            use 4
            norm_num
            rw [lk]
            norm_num
        .
            have sk: 0 < k := by omega
            clear sk
            by_cases lk: k = 1
            .
                simp [lk]
                use 2
                norm_num
            .
                have ok: 2 ≤ k := by omega
                clear lk
                by_cases lk: k = 2
                .
                    simp [lk]
                    use 1
                    norm_num
                .
                    replace lk: 3 ≤ k := by omega
                    clear hk
                    have ok: 0 < k := by omega
                    simp [ok] at ih
                    clear ok
                    obtain ⟨n, h, hn⟩ := ih
                    replace h: ∃ a: ℤ, 0 < a ∧ a ^ 2 = n * 2 ^ k - 7 := by   -- use induction
                        apply IsSquare.exists_sq at h
                        obtain ⟨r, h⟩ := h
                        by_cases lr: 0 < r
                        .
                            use r
                            simp [lr]
                            rw [← h]
                        .
                            have or: r ≠ 0 := by
                                by_contra! or
                                simp [or] at h
                                replace h: n * 2 ^ k = 7 := by omega
                                have o: (2: ℤ) ∣ 7 := by
                                    rw [← h]
                                    have s: (2: ℤ) ^ k = 2 * 2 ^ (k - 1) := by
                                        nth_rewrite 1 [show k = k - 1 + 1 by omega]
                                        ring
                                    rw [s]
                                    ring_nf
                                    simp
                                norm_num at o
                            replace lr: r < 0 := by omega
                            clear or
                            use -r
                            have o: 0 < -r := by linarith
                            simp [o]
                            rw [← h]

                    obtain ⟨a, ha, h⟩ := h
                    by_cases dn: Even n

                    -- case n is even
                    .
                        use n / 2
                        constructor
                        .
                            have o: n / 2 * 2 = n := by
                                rw [Int.ediv_mul_cancel]
                                apply Even.two_dvd at dn
                                exact dn
                            rw [show (2: ℤ) ^ (k + 1) = 2 * 2 ^ k by ring]
                            rw [show n / 2 * (2 * 2 ^ k) = n / 2 * 2 * 2 ^ k by ring]
                            rw [o]
                            rw [← h]
                            apply IsSquare.sq
                        . have s: 2 ≤ n := by
                            by_contra! s
                            replace s: n = 1 := by omega
                            simp [s] at dn
                          omega

                    -- case n is odd
                    .
                        simp at dn
                        set m:= (2: ℤ) ^ (k - 1) with hm
                        clear_value m

                        -- we then show that a + m is as desired
                        have f: (a + m) ^ 2 = n * 2 ^ k - 7 + m * (m + 2 * a) := by
                            ring_nf
                            rw [h]
                            ring
                        have g: m * (m + 2 * a) = 2 ^ k * (2 ^ (k - 2) + a) := by
                            rw [hm]
                            have o: (2: ℤ) ^ (k - 1) = 2 * (2 ^ (k - 2)) := by
                                nth_rewrite 1 [show k - 1 = k - 2 + 1 by omega]
                                ring
                            have o1: (2: ℤ) ^ k = 2 * 2 ^ (k - 1) := by
                                nth_rewrite 1 [show k = k - 1 + 1 by omega]
                                ring
                            rw [o1]
                            rw [o]
                            ring
                        rw [g] at f
                        rw [show n * 2 ^ k - 7 + 2 ^ k * (2 ^ (k - 2) + a) =  (n + 2 ^ (k - 2) + a) * 2 ^ k - 7 by ring] at f

                        -- then we show the thing in the bracket is even
                        have s: Even (n + 2 ^ (k - 2) + a) := by
                            rw [Int.even_add']
                            have o1: Odd (n + 2 ^ (k - 2)) := by
                                apply Odd.add_even
                                exact dn
                                have s: (2: ℤ) ^ (k - 2) = 2 * 2 ^ (k - 3) := by
                                    nth_rewrite 1 [show k - 2 = k - 3 + 1 by omega]
                                    ring
                                rw [s]
                                simp
                            have o2: Odd a := by
                                have o3: Odd (a ^ 2) := by
                                    rw [h]
                                    apply Even.sub_odd
                                    have s: (2: ℤ) ^ k = 2 * 2 ^ (k - 1) := by
                                        nth_rewrite 1 [show k = k - 1 + 1 by omega]
                                        ring
                                    rw [s]
                                    simp
                                    decide
                                rw [show a ^ 2 = a * a by ring] at o3
                                apply Int.Odd.of_mul_left o3
                            simp [o1, o2]
                        rw [even_iff_exists_two_mul] at s
                        obtain ⟨t, ht⟩ := s
                        rw [ht] at f
                        rw [show 2 * t * 2 ^ k = (t * 2 ^ (k + 1)) by ring] at f
                        use t
                        constructor
                        .
                            rw [← f]
                            apply IsSquare.sq
                        .
                            by_contra! o
                            nlinarith
                            