import Mathlib

/-What is the smallest prime number that is the sum of three different prime numbers? A 11 B 15 C 17 D 19 E 23-/

theorem number_theory_236037: IsLeast {n: ℕ | Nat.Prime n ∧
  ∃ p q r, p < q ∧ q < r ∧ Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ n = p + q + r} 19 := by

  constructor

  -- the forward direction
  .
    simp
    norm_num
    use 3
    use 5
    norm_num
    use 11
    norm_num

  -- the backward direction
  .
    intro n h
    by_contra! l
    simp only [Set.mem_setOf_eq] at h
    rcases h with ⟨hn, h⟩
    obtain ⟨p, q, r, hpq, hqr, hp, hq, hr, h⟩ := h

    -- we show that n is at least 10
    have lp: 2 ≤ p := by
      by_contra! lp
      interval_cases p
      all_goals norm_num at hp
    have lq: 3 ≤ q := by
      by_contra! lq
      interval_cases q
      all_goals norm_num at hq
      .
        omega
    have lr: 5 ≤ r := by
      by_contra! lr
      interval_cases r
      all_goals norm_num at hr
      .
        omega
      .
        omega
    have ln: 10 ≤ n := by omega

    -- then we check one by one from 10 to 18
    interval_cases n

    -- first tackle the cases n is not prime
    all_goals try norm_num at hn

    -- n = 11
    .
      have rp: p ≤ 3 := by omega
      interval_cases p
      .
        replace h: q + r = 9 := by omega
        have rq: q ≤ 4 := by omega
        interval_cases q
        .
          replace h: r = 6 := by omega
          simp [h] at hr
          norm_num at hr
        .
          norm_num at hq
      .
        replace h: q + r = 8 := by omega
        have rq: q ≤ 3 := by omega
        have v: q = 3 := by omega
        simp [v] at hpq

    -- n = 13
    .
      have rp: p ≤ 4 := by omega
      interval_cases p
      .
        replace h: q + r = 11 := by omega
        have rq: q ≤ 5 := by omega
        interval_cases q
        .
          replace h: r = 8 := by omega
          simp [h] at hr
          norm_num at hr
        .
          norm_num at hq
        .
          replace h: r = 6 := by omega
          simp [h] at hr
          norm_num at hr
      .
        replace h: q + r = 10 := by omega
        have rq: q ≤ 4 := by omega
        have v: q = 4 := by omega
        simp [v] at hq
        norm_num at hq
      .
        norm_num at hp

    -- n = 17
    .
      have rp: p ≤ 4 := by omega
      interval_cases p
      .
        replace h: q + r = 15 := by omega
        have rq: q ≤ 7 := by omega
        interval_cases q
        all_goals try norm_num at hq
        .
          replace h: r = 12 := by omega
          simp [h] at hr
          norm_num at hr
        .
          replace h: r = 10 := by omega
          simp [h] at hr
          norm_num at hr
        .
          replace h: r = 8 := by omega
          simp [h] at hr
          norm_num at hr
      .
        replace h: q + r = 14 := by omega
        have rq: q ≤ 6 := by omega
        interval_cases q
        all_goals try norm_num at hq
        .
          replace h: r = 9 := by omega
          simp [h] at hr
          norm_num at hr
      .
        norm_num at hp
        