import Mathlib

/-Yura wrote down a four-digit number. Lenya added 1 to the first digit of this number, 2 to the second, 3 to the third, and 4 to the fourth, and then multiplied the resulting sums. Lenya got 234. What number could Yura have written down-/

theorem number_theory_215847: {n: ℕ | ∃ a b c d: ℕ, 1 ≤ a ∧ a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9 ∧ d ≤ 9
 ∧ n = 1000 * a + 100 * b + 10 * c + d ∧ (a + 1) * (b + 2) * (c + 3) * (d + 4) = 234} = {2009, 1109} := by

  ext n
  simp only [Set.mem_setOf_eq]
  constructor
  
  -- the forward direction
  .
    intro h
    obtain ⟨a, b, c, d, la1, la2, lb, lc, ld, hn, h⟩ := h

    -- we show that d = 9
    have hd: d = 9 := by
      by_contra! o
      replace o: d ≤ 8 := by omega
      replace h: 13 ∣ (a + 1) * (b + 2) * (c + 3) * (d + 4) := by
        rw [h]
        norm_num
      rw [Nat.Prime.dvd_mul] at h
      rcases h with h | h
      .
        rw [Nat.Prime.dvd_mul] at h
        rcases h with h | h
        .
          rw [Nat.Prime.dvd_mul] at h
          rcases h with h | h
          .
            apply Nat.le_of_dvd at h
            linarith
            omega
          .
            apply Nat.le_of_dvd at h
            linarith
            omega
          norm_num
        .
          apply Nat.le_of_dvd at h
          linarith
          omega
        norm_num
      .
        apply Nat.le_of_dvd at h
        linarith
        omega
      norm_num

    simp [hd] at *
    replace h: (a + 1) * (b + 2) * (c + 3) = 18 := by omega

    -- then we show that c = 0
    have hc: c = 0 := by
      have l: c < 2 := by
        by_contra! l
        have l1: 4 ≤ (a + 1) * (b + 2) := by nlinarith
        have l2: 20 ≤ (a + 1) * (b + 2) * (c + 3) := by
          have s: 5 ≤ c + 3 := by nlinarith
          nlinarith
        rw [h] at l2
        norm_num at l2
      interval_cases c
      .
        simp
      .
        rw [show 1 + 3 = 4 by rfl] at h
        have o: 4 ∣ 18 := by
          rw [← h]
          simp
        norm_num at o

    simp [hc] at *
    replace h: (a + 1) * (b + 2) = 6 := by omega

    -- tben b ≤ 1
    have hb: b < 2 := by
      by_contra! l
      nlinarith
    interval_cases b
    .
      replace h: a = 2 := by omega
      left
      simp [h] at *
      exact hn
    .
      replace h: a = 1 := by omega
      right
      simp [h] at *
      exact hn

  -- the backward direction
  .
    intro h
    simp at h
    rcases h with h | h
    .
      simp [h]
      use 2
      norm_num
      use 0
      norm_num
      use 0
      norm_num
      use 9
    .
      simp [h]
      use 1
      norm_num
      use 1
      norm_num
      use 0
      norm_num
      use 9