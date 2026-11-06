import Mathlib

/-Among all the factors of 11!(11!=11×10×⋯×1),
the largest factor that can be expressed as 6k+1
(where k is a natural number) is -/

theorem number_theory_252652: IsGreatest {n: ℕ | n ∣ Nat.factorial 11 ∧ ∃ k, n = 6 * k + 1} 385 := by

  constructor
  -- show that 385 is in the set
  .
    constructor
    -- show that 385 is a factor of 11!
    .
      decide
    -- show that 385 is of the form 6k + 1
    .
      use 64

  -- show that 385 is the largest element
  .
    intro n h
    simp at h
    rcases h with ⟨h, d⟩
    obtain ⟨k, d⟩ := d
    replace d: 6 ∣ n + 5 := by
      rw [d]
      simp
    have eq: Nat.factorial 11 = 2 ^ 8 * 3 ^ 4 * 1925:= by
      decide
    rw [eq] at h
    clear eq

    -- show n is coprime with 2
    have o2: Nat.Coprime n 2 := by
        apply Nat.Coprime.symm
        rw [Nat.Prime.coprime_iff_not_dvd]
        .
          by_contra! t
          replace d: 2 ∣ n + 5 := by
            have i: 2 ∣ 6 := by norm_num
            apply dvd_trans i d
          have o: 2 ∣ 5 := by
            rw [show 5 = n + 5 - n by omega]
            apply Nat.dvd_sub
            omega
            exact d
            exact t
          norm_num at o
        .
          norm_num

  -- show n is coprime with 3
    have o3: Nat.Coprime n 3 := by
        apply Nat.Coprime.symm
        rw [Nat.Prime.coprime_iff_not_dvd]
        .
          by_contra! t
          replace d: 3 ∣ n + 5 := by
            have i: 3 ∣ 6 := by norm_num
            apply dvd_trans i d
          have o: 3 ∣ 5 := by
            rw [show 5 = n + 5 - n by omega]
            apply Nat.dvd_sub
            omega
            exact d
            exact t
          norm_num at o
        .
          norm_num

    -- note that n is coprime with 6, hence we have n ∣ 1925
    replace h: n ∣ 1925 := by
      apply Nat.Coprime.dvd_of_dvd_mul_left at h
      exact h
      apply Nat.Coprime.mul_right
      .
        apply Nat.Coprime.pow_right
        exact o2
      .
        apply Nat.Coprime.pow_right
        exact o3

    -- then we can check the factors of 1925
    replace h: n ∈ Nat.divisors 1925 := by
      simp
      exact h
    have eq: Nat.divisors 1925 = {1, 5, 7, 11, 25, 35, 55, 77, 175, 275, 385, 1925} := by
      native_decide
    rw [eq] at h
    clear eq
    simp at h
    by_contra! o
    have i: n ≠ 1925 := by
      by_contra! i
      simp [i] at d
      norm_num at d
    omega
    