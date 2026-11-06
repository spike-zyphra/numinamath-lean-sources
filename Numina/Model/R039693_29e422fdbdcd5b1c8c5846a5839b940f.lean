import Mathlib

theorem number_theory_14712 (s : Set ℕ) (hs : s = {n : ℕ | 0 < n ∧ n.lcm 100 = n.gcd 100 + 450}) :
    ∑ᶠ x ∈ s, x = 250 := by 
  have h1 : s = {n : ℕ | 0 < n ∧ n.lcm 100 = n.gcd 100 + 450} := by 
    exact_mod_cast hs
  have h15 : s = {250} := by 
    ext n 
    simp [h1]
    constructor 
    · -- Assume h, need show n = 250 
      intro h 
      rcases h with ⟨hn_pos, h_eq⟩ 
      have h3 : n > 0 := hn_pos 
      by_cases h4 : n ≤ 1000 
      · -- n ≤ 1000 
        interval_cases n <;> norm_num [Nat.lcm, Nat.gcd] at h_eq ⊢ 
      · -- n > 1000 
        have h5 : n.gcd 100 ∣ 100 := Nat.gcd_dvd_right n 100 
        have h6 : n.gcd 100 ∣ n := Nat.gcd_dvd_left n 100 
        have h7 : n.gcd 100 ≤ 100 := by 
          exact Nat.le_of_dvd (by norm_num) h5 
        have h8 : n.lcm 100 = n.gcd 100 + 450 := by 
          linarith [h_eq] 
        have h9 : n.lcm 100 = n * 100 / n.gcd 100 := by 
          rfl 
        have h10 : n * 100 / n.gcd 100 = n.gcd 100 + 450 := by 
          rw [h9] at h8 
          omega 
        have h14 : n.gcd 100 > 0 := by 
          by_contra h 
          push_neg at h 
          have h15 : n.gcd 100 = 0 := by 
            omega 
          have h16 : n.gcd 100 ∣ 100 := by 
            apply Nat.gcd_dvd_right 
          rw [h15] at h16 
          norm_num at h16 
        have h11 : n * 100 = n.gcd 100 * (n.gcd 100 + 450) := by
          have h13 : n.gcd 100 ∣ n * 100 := by
            have h17 : n.gcd 100 ∣ n := by
              exact Nat.gcd_dvd_left n 100
            have h19 : n.gcd 100 ∣ n * 100 := by 
              exact Nat.dvd_trans h17 (by simp [show n * 100 = n * (100) by omega])
            exact h19 
          have h13' : n * 100 = n.gcd 100 * (n * 100 / n.gcd 100) := by 
            rw [Nat.mul_div_cancel']
            all_goals 
              omega 
          rw [show n * 100 / n.gcd 100 = n.gcd 100 + 450 by omega] at h13' 
          linarith 
        interval_cases h2 : n.gcd 100 <;> omega 
    · -- Show 250 is in s 
      intro h 
      rw [h] 
      constructor 
      · norm_num 
      · norm_num [Nat.lcm, Nat.gcd] 
  rw [h15]
  rw [finsum_mem_singleton]
  all_goals norm_num