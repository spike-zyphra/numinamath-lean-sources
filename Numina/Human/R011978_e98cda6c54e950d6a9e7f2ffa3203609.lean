import Mathlib

/-Determine all four-digit natural numbers that have the property of
being divisible by each of the numbers 2,3,4,5,6,7,8,9,10,12,14,15!-/

theorem number_theory_169734: {n: ℕ | 1000 ≤ n ∧ n < 10000 ∧
2 ∣ n ∧ 3 ∣ n ∧ 4 ∣ n ∧ 5 ∣ n ∧ 6 ∣ n ∧ 7 ∣ n ∧ 8 ∣ n ∧ 9 ∣ n ∧ 10 ∣ n ∧ 12 ∣ n ∧ 14 ∣ n ∧ 15 ∣ n}
  = {2520, 5040, 7560} := by

    ext n
    constructor

    -- the forward direction
    .
      intro h
      simp only [Set.mem_setOf_eq] at h
      rcases h with ⟨l, r, d2, d3, d4, d5, d6, d7, d8, d9, d10, d12, d14, d15⟩

      -- note that 7 and 9 are coprime, hence 63 ∣ n
      have u: 7 * 9 ∣ n := by
        apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
        norm_num
        exact d7
        exact d9
      norm_num at u

      -- further we have 5 * 63 ∣ n
      replace u: 5 * 63 ∣ n := by
        apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
        norm_num
        exact d5
        exact u
      norm_num at u

      -- further 8 * 315 ∣ n
      replace u: 8 * 315 ∣ n := by
        apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
        norm_num
        exact d8
        exact u
      norm_num at u

      apply exists_eq_mul_right_of_dvd at u
      obtain ⟨k, h⟩ := u
      have lk: 1 ≤ k := by
        by_contra! o
        replace o: k = 0 := by
          clear * - o
          omega
        simp [o] at h
        simp [h] at l
      have rk: k < 4 := by nlinarith
      interval_cases k
      .
        simp [h]
      .
        simp [h]
      .
        simp [h]

    -- the backward direction
    .
      intro h
      simp at h
      rcases h with h | h | h
      all_goals simp [h]; norm_num