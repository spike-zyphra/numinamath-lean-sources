import Mathlib

/- Let $ p,q,r$ be 3 prime numbers such that $ 5\leq p < q < r$.
Knowing that $ 2p^2-r^2 \geq 49$ and $ 2q^2 -r^2\leq 193$,
find $ p,q,r$. -/

theorem number_theory_28369 (p q r: ℤ) (hp: Prime p) (hq: Prime q) (hr: Prime r)
    (l1: 5 ≤ p) (l2: p < q) (l3: q < r) (h1: 2 * p ^ 2 - r ^ 2 ≥ 49)
    (h2: 2 * q ^ 2 - r ^ 2 ≤ 193): p = 17 ∧ q = 19 ∧ r = 23 := by

    -- we first show that p is at least 11
    have lp: 11 ≤ p := by
        by_contra! o
        have t: p ≠ 10 := by
            by_contra! s
            simp [s] at hp
            norm_num at hp
        replace o: p ≤ 9 := by omega
        have lr: r < 11 := by nlinarith -- from h1
        replace lr: r ≤ 7 := by
            by_contra! f
            interval_cases r
            all_goals norm_num at hr
        have eq: q = 6 := by omega  --then q = 6
        simp [eq] at hq
        norm_num at hq

    -- then we show that p, q are odd
    have op: Odd p := by
        rw [← Int.natAbs_odd]
        apply Nat.Prime.odd_of_ne_two
        rw [← Int.prime_iff_natAbs_prime]
        exact hp
        zify
        rw [show |p| = p by apply abs_of_nonneg; linarith]
        linarith
    have oq: Odd q := by
        rw [← Int.natAbs_odd]
        apply Nat.Prime.odd_of_ne_two
        rw [← Int.prime_iff_natAbs_prime]
        exact hq
        zify
        rw [show |q| = q by apply abs_of_nonneg; linarith]
        linarith

    -- we give a lower bound for q
    have vq: 13 ≤ q := by
        have o: q ≠ 12 := by
            by_contra! s
            simp [s] at hq
            norm_num at hq
        omega


    -- from h1 and h2, we get l:
    have l: 2 * q ^ 2 - 193 ≤ 2 * p ^ 2 - 49 := by nlinarith
    replace l: (q + p) * (q - p) ≤ 72 := by linarith

    -- then we must have q ≤ 25
    have lq: q ≤ 25 := by
        by_contra! t
        replace t: 37 ≤ p + q := by omega
        have o: q - p < 2 := by nlinarith
        replace o: q = p + 1 := by omega
        have eq: Even q := by
            rw [o]
            rw [Int.even_add_one]
            simp
            exact op
        absurd eq
        simp
        exact oq


    apply Odd.exists_bit1 at oq
    obtain ⟨k, hk⟩ := oq
    have lk: 6 ≤ k := by omega
    have rk: k ≤ 12 := by omega

    -- then we check the possible values of k
    interval_cases k
    all_goals simp [hk] at hq
    all_goals norm_num at hq
    -- q = 13
    .
        norm_num at hk
        simp [hk] at *
        clear l1
        -- then p = 11
        have ep: p = 11 := by
            by_contra! s
            replace s: p = 12 := by omega
            simp [s] at hp
            norm_num at hp
        simp [ep] at h1
        nlinarith -- from 13 < r and h1
    -- q = 17
    .
        norm_num at hk
        simp [hk] at *
        clear l1
        -- then p = 13
        have ep: p = 11 ∨ p = 13 := by
            interval_cases p
            all_goals norm_num at hp
            all_goals omega
        rcases ep with g | g
        .
            simp [g] at l
        .
            simp [g] at l
    -- q = 19
    .
        norm_num at hk
        simp [hk] at *
        clear l1
        -- then 15 < p
        have sp: 15 < p := by nlinarith -- from l
        interval_cases p
        all_goals norm_num at hp
        norm_num
        nlinarith
    -- q = 23
    .
        norm_num at hk
        simp [hk] at *
        clear l1
        -- then 21 < p
        have sp: 21 < p := by nlinarith -- from l
        have o: p = 22 := by omega
        simp [o] at hp
        norm_num at hp
        