import Mathlib

/-find all natural numbers a,b and n
so that the following equation holds
  a! + b! = 2 ^ n -/

theorem number_theory_266745: {(a, b, n): ℕ × ℕ × ℕ | a.factorial + b.factorial = 2 ^ n} =
    {(0, 0, 1), (0, 1, 1), (1, 0, 1), (1, 1, 1), (2, 2, 2), (2, 3, 3), (3, 2, 3)} := by

  ext ⟨a, b, n⟩
  constructor
  -- the forward direction
  .
    intro h
    simp at h
    by_cases l: a ≤ b
    -- case 1: a ≤ b
    .
      -- we show that a ≤ 2
      have la: a < 3 := by
        by_contra! o
        have i: 3 ∣ a.factorial := by
          apply Nat.dvd_factorial
          omega
          omega
        have j: 3 ∣ b.factorial := by
          apply Nat.dvd_factorial
          omega
          omega
        have s: 3 ∣ 2 ^ n := by
          rw [← h]
          apply Nat.dvd_add
          exact i
          exact j
        have o: Nat.Prime 3 := by
          norm_num
        have c:= Nat.Prime.dvd_of_dvd_pow o s
        norm_num at c

      -- hence a = 0, 1, 2
      interval_cases a

      -- a = 0
      .
        simp at h
        by_cases ln: 1 ≤ n
        .
          -- then b = 0 ∨ 1
          have lb: b < 2 := by
            by_contra! o
            have s: 2 ∣ 2 ^ n := by
              rw [show n = n - 1 + 1 by omega]
              rw [Nat.pow_add]
              norm_num
            rw [← h] at s
            have i: 2 ∣ b.factorial := by
              apply Nat.dvd_factorial
              omega
              omega
            have j: 2 ∣ 1 := by
              rw [show 1 = 1 + b.factorial - b.factorial by omega]
              apply Nat.dvd_sub
              omega
              exact s
              exact i
            norm_num at j
          interval_cases b
          .
            simp at h
            symm at h
            rw [Nat.pow_eq_self_iff] at h
            simp [h]
            norm_num
          .
            simp at h
            symm at h
            rw [Nat.pow_eq_self_iff] at h
            simp [h]
            norm_num
        .
          -- n = 0
          simp at ln
          simp [ln] at h
          have s:= Nat.factorial_ne_zero b
          simp [h] at s

      -- a = 1, just the same as above
      .
        simp at h
        by_cases ln: 1 ≤ n
        .
          -- then b = 0 ∨ 1
          have lb: b < 2 := by
            by_contra! o
            have s: 2 ∣ 2 ^ n := by
              rw [show n = n - 1 + 1 by omega]
              rw [Nat.pow_add]
              norm_num
            rw [← h] at s
            have i: 2 ∣ b.factorial := by
              apply Nat.dvd_factorial
              omega
              omega
            have j: 2 ∣ 1 := by
              rw [show 1 = 1 + b.factorial - b.factorial by omega]
              apply Nat.dvd_sub
              omega
              exact s
              exact i
            norm_num at j
          interval_cases b
          .
            simp at h
            symm at h
            rw [Nat.pow_eq_self_iff] at h
            simp [h]
            norm_num
        .
          -- n = 0
          simp at ln
          simp [ln] at h
          have s:= Nat.factorial_ne_zero b
          simp [h] at s

      -- a = 2
      .
        simp at h
        by_cases ln: 2 ≤ n
        .
          have l: b < 4 := by
            by_contra! r
            have q: 4 ∣ b.factorial := by
              apply Nat.dvd_factorial
              omega
              omega
            have s: 4 ∣ 2 ^ n := by
              rw [show n = n - 2 + 2 by omega]
              rw [Nat.pow_add]
              norm_num
            rw [← h] at s
            have c: 4 ∣ 2 := by
              rw [show 2 = 2 + b.factorial - b.factorial by omega]
              apply Nat.dvd_sub
              omega
              exact s
              exact q
            norm_num at c
          interval_cases b
          .
            simp at h
            symm at h
            rw [show 4 = 2 ^ 2 by norm_num] at h
            rw [pow_right_inj₀] at h
            simp [h]
            norm_num
            norm_num
          .
            rw [show Nat.factorial 3 = 6 by decide] at h
            simp at h
            rw [show 8 = 2 ^ 3 by norm_num] at h
            rw [pow_right_inj₀] at h
            simp [h]
            norm_num
            norm_num
        .
          -- n = 0
          simp at ln
          interval_cases n
          .
            simp at h
            omega
          .
            simp at h
            have s:= Nat.factorial_ne_zero b
            simp [h] at s

    -- case 2: a > b
    .
      simp at l
      -- we show that b ≤ 2
      have lb: b < 3 := by
        by_contra! o
        have i: 3 ∣ b.factorial := by
          apply Nat.dvd_factorial
          omega
          omega
        have j: 3 ∣ a.factorial := by
          apply Nat.dvd_factorial
          omega
          omega
        have s: 3 ∣ 2 ^ n := by
          rw [← h]
          apply Nat.dvd_add
          exact j
          exact i
        have o: Nat.Prime 3 := by
          norm_num
        have c:= Nat.Prime.dvd_of_dvd_pow o s
        norm_num at c

      -- hence b = 0, 1, 2
      interval_cases b

      -- b = 0, just the same as above
      .
        simp at h
        by_cases ln: 1 ≤ n
        .
          -- then a = 0 ∨ 1
          have la: a < 2 := by
            by_contra! o
            have s: 2 ∣ 2 ^ n := by
              rw [show n = n - 1 + 1 by omega]
              rw [Nat.pow_add]
              norm_num
            rw [← h] at s
            have i: 2 ∣ a.factorial := by
              apply Nat.dvd_factorial
              omega
              omega
            have j: 2 ∣ 1 := by
              rw [show 1 = a.factorial + 1 - a.factorial by omega]
              apply Nat.dvd_sub
              omega
              exact s
              exact i
            norm_num at j

          interval_cases a
          .
            simp at h
            symm at h
            rw [Nat.pow_eq_self_iff] at h
            simp [h]
            norm_num

        .
          -- n = 0, just the same as above.
          simp at ln
          simp [ln] at h
          have s:= Nat.factorial_ne_zero a
          simp [h] at s

      -- b = 1, just the same as above
      .
        simp at h
        by_cases ln: 1 ≤ n
        .
          -- then a = 0 ∨ 1
          have la: a < 2 := by
            by_contra! o
            have s: 2 ∣ 2 ^ n := by
              rw [show n = n - 1 + 1 by omega]
              rw [Nat.pow_add]
              norm_num
            rw [← h] at s
            have i: 2 ∣ a.factorial := by
              apply Nat.dvd_factorial
              omega
              omega
            have j: 2 ∣ 1 := by
              rw [show 1 = a.factorial + 1 - a.factorial by omega]
              apply Nat.dvd_sub
              omega
              exact s
              exact i
            norm_num at j

          omega
        .
          -- n = 0, just the same as above
          simp at ln
          simp [ln] at h
          have s:= Nat.factorial_ne_zero a
          simp [h] at s

      -- b = 2, just the same as above
      .
        simp at h
        by_cases ln: 2 ≤ n
        .
          -- then a < 4
          have l: a < 4 := by
            by_contra! r
            have q: 4 ∣ a.factorial := by
              apply Nat.dvd_factorial
              omega
              omega
            have s: 4 ∣ 2 ^ n := by
              rw [show n = n - 2 + 2 by omega]
              rw [Nat.pow_add]
              norm_num
            rw [← h] at s
            have c: 4 ∣ 2 := by
              rw [show 2 = a.factorial + 2 - a.factorial by omega]
              apply Nat.dvd_sub
              omega
              exact s
              exact q
            norm_num at c

          interval_cases a
          .
            rw [show Nat.factorial 3 = 6 by decide] at h
            simp at h
            rw [show 8 = 2 ^ 3 by norm_num] at h
            rw [pow_right_inj₀] at h
            simp [h]
            norm_num
            norm_num

        .
          -- n = 0, just the same as above
          simp at ln
          interval_cases n
          .
            simp at h
          .
            simp at h
            have s:= Nat.factorial_ne_zero a
            simp [h] at s


  -- the backward direction
  .
    intro h
    simp at h
    rcases h with h | h | h | h | h | h | h
    all_goals simp [h]
    all_goals decide