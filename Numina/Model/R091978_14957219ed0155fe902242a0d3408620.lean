import Mathlib

theorem number_theory_103944 : IsGreatest {x | ∀ n : ℤ, x ∣ (n ^ 7 - n)} 42 := by
  constructor
  · -- Show that 42 is in the set
    intro n
    have h1 : n ^ 7 % 2 = n % 2 := by
      have h1 : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases h1 with (h1 | h1)
      ·
        simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      ·
        simp [h1, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]

    have h2 : n ^ 7 % 3 = n % 3 := by
      have h2 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
      rcases h2 with (h2 | h2 | h2)
      ·
        simp [h2, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      ·
        simp [h2, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      ·
        simp [h2, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]

    have h3 : n ^ 7 % 7 = n % 7 := by
      have h3 : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by omega
      rcases h3 with (h3 | h3 | h3 | h3 | h3 | h3 | h3)
      ·
        simp [h3, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      ·
        simp [h3, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      ·
        simp [h3, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      ·
        simp [h3, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      ·
        simp [h3, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      ·
        simp [h3, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
      ·
        simp [h3, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]

    have h4 : (n ^ 7 - n) % 42 = 0 := by
      omega

    exact Int.dvd_of_emod_eq_zero h4
  · -- Show that 42 is the greatest
    intro x hx
    have h2 := hx 2
    have h3 := hx 3
    have h4 := hx 4
    have h5 := hx 6
    norm_num at h2 h3 h4 h5
    -- Use bounds from h2, h3, h4, h5 to prove x ≤ 42
    have h10 : x ∣ 42 := by
      -- x divides 42
      exact Int.dvd_gcd (Int.dvd_gcd (Int.dvd_gcd h2 h3) h4) h5
    have h11 : x ≤ 42 := by 
      exact Int.le_of_dvd (by norm_num) h10
    linarith