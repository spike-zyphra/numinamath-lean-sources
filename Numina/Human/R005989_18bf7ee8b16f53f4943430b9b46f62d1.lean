import Mathlib

open Finset Real Nat

/-Find the sum of the even positive divisors of 1000-/
theorem Number_Theory_610975: (∑ d ∈ divisors 1000, if d % 2 = 0 then d else 0) = 2184 := by
  have h1000 : 1000 = 2^3 * 5^3 := by norm_num  -- Factorize 1000 = 2^3 * 5^3
  -- Generate all divisors of 1000
  have h_divisors : divisors 1000 = {1, 2, 4, 5, 8, 10, 20, 25, 40, 50, 100, 125, 200, 250, 500, 1000} := by
    simp [h1000, divisors]
    ext a
    simp
    constructor
    . intro ha
      rcases ha with ⟨b, hb⟩
      by_cases h5: 5 ∣ a
      -- case: 5∣a --
      . apply exists_eq_mul_right_of_dvd at h5
        rcases h5 with ⟨c, hc⟩
        rw [hc]
        rw [hc] at hb
        replace hb: c ∣ 200 := by
          rw [show 1000 = 5 * 200 by omega] at hb
          apply Nat.dvd_of_mul_dvd_mul_left at hb
          exact hb
          linarith
        have hb2:= hb
        apply Nat.le_of_dvd at hb
        have b1: c ∈ Icc 1 200 := by
          simp
          omega
        fin_cases b1
        all_goals omega
      -- case: ¬ 5∣a --
      . have cop: a.Coprime 125 := by
          have cop5: a.Coprime 5 := by
            rw [coprime_iff_gcd_eq_one]
            -- The gcd of 5 and a divides 5 (since gcd is a divisor)
            have h_gcd_dvd : a.gcd 5 ∣ 5 := by apply Nat.gcd_dvd_right
            -- Since 5 is prime, its only divisors are 1 and 5
            let c := a.gcd 5
            have eq: a.gcd 5 = c := by omega
            have hc : c ∣ 5 := by
              simp [c,h_gcd_dvd]
            -- Since c ∣ 5 and c ≠ 1, c must be 5
            have hc2: 1 ≤ c := by
                by_contra! hc2
                replace hc2: c = 0 := by omega
                simp [c] at hc2
                apply Nat.eq_zero_of_gcd_eq_zero_left at hc2
                omega
            have hc2:= hc
            apply Nat.le_of_dvd at hc
            have hc3: c ∈ Icc 1 5 := by
                simp
                omega
            rw [eq]
            clear_value c
            fin_cases hc3
            . omega
            . omega
            . omega
            . omega
            . simp at *
              have q : a.gcd 5 ∣ a := by apply Nat.gcd_dvd_left
              rw [eq] at q
              omega
            . omega
          rw [show 125 = 5^3 by norm_num]
          apply Nat.Coprime.pow_right
          exact cop5
        rw [show 1000 = 125 * 8 by norm_num] at hb
        apply Nat.Coprime.dvd_of_dvd_mul_left at hb
        have hb2:= hb
        apply Nat.le_of_dvd at hb
        have b1: a ∈ Icc 1 8 := by
          simp
          omega
        fin_cases b1
        all_goals omega
    . intro h
      constructor
      . omega
      . rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
        all_goals rw [h]
        all_goals omega
  rw [h_divisors]
  simp