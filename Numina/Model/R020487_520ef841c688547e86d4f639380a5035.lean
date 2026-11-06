import Mathlib

theorem number_theory_1121 : IsGreatest {k | ∀ n : ℤ, ¬Prime n → k ∣ n ^ 3 - n} 6 := by 
  constructor
  · -- Show that 6 is in the set.
    show ∀ n : ℤ, ¬Prime n → 6 ∣ n ^ 3 - n
    intro n hn
    have h1 : n ^ 3 % 6 = n % 6 := by
      have h2 : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by
        omega
      rcases h2 with (h | h | h | h | h | h) <;> simp [h, pow_succ, Int.add_emod, Int.mul_emod]
    have h2 : (n ^ 3 - n) % 6 = 0 := by
      omega
    exact Int.dvd_of_emod_eq_zero h2
  · -- Show that 6 is greatest in the set
    intro k hk
    have h1 := hk 4 (by 
      norm_num [Int.prime_iff_natAbs_prime]
    )
    have h2 := hk 6 (by 
      norm_num [Int.prime_iff_natAbs_prime]
    )
    have h3 := hk 8 (by 
      norm_num [Int.prime_iff_natAbs_prime]
    )
    have h4 := hk 0 (by 
      norm_num [Int.prime_iff_natAbs_prime]
    )
    have h5 := hk 1 (by 
      norm_num [Int.prime_iff_natAbs_prime]
    )
    norm_num at h1 h2 h3 h4 h5
    have h6 : k ∣ 6 := by 
      exact Int.dvd_gcd (Int.dvd_gcd h1 h2) h3
    have h7 : k ≤ 6 := by
      apply Int.le_of_dvd (show 0 < (6 : ℤ) by norm_num) h6
    linarith