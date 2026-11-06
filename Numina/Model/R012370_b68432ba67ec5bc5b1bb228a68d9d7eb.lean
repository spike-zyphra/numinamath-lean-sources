import Mathlib

theorem number_theory_100345 (n : ℤ) : IsGreatest {k | ∀ n : ℤ, k ∣ n^3 - n} 6 := by
  constructor
  · -- Show 6 is indeed in the set.
    intro n
    have h1 : n ^ 3 % 6 = n % 6 := by
      have h2 : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by
        omega
      rcases h2 with (h | h | h | h | h | h)
      · 
        simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
        all_goals omega
      · 
        simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
        all_goals omega
      · 
        simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
        all_goals omega
      · 
        simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
        all_goals omega
      · 
        simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
        all_goals omega
      · 
        simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod]
        all_goals omega
    have h2 : (n ^ 3 - n) % 6 = 0 := by
      have h3 : n ^ 3 % 6 = n % 6 := h1
      omega
    exact Int.dvd_of_emod_eq_zero h2
  · -- Show 6 is the greatest such integer.
    intro k hk
    have h1 := hk 2
    have h2 : k ∣ 6 := by
      exact h1
    have h3 : k ≤ 6 := by
      exact Int.le_of_dvd (show 0 < 6 by norm_num) h2
    linarith