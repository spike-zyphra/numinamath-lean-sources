import Mathlib

def S : Set ℤ := {n | ∃ m : ℤ, n = m^5 - 5 * m^3 + 4 * m ∧ ¬3 ∣ m}

theorem number_theory_47269 :
    IsGreatest {k | ∀ n ∈ S, k ∣ n} 360 := by
  constructor 
  · -- Show 360 is in the set.
    intro n hn
    rcases hn with ⟨m, hm, hm1⟩
    have h1 : m % 3 = 1 ∨ m % 3 = 2 := by 
      omega
    have h2 : (m^5 - 5 * m^3 + 4 * m) % 8 = 0 := by
      have h11 : m % 8 = 0 ∨ m % 8 = 1 ∨ m % 8 = 2 ∨ m % 8 = 3 ∨ m % 8 = 4 ∨ m % 8 = 5 ∨ m % 8 = 6 ∨ m % 8 = 7 := by 
        omega
      rcases h11 with (h | h | h | h | h | h | h | h) <;> simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod] <;> omega
    have h5 : (m^5 - 5 * m^3 + 4 * m) % 5 = 0 := by
      have h1' : m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 ∨ m % 5 = 4 := by 
        omega
      rcases h1' with (h | h | h | h | h) <;> simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod] <;> omega
    have h6 : (m^5 - 5 * m^3 + 4 * m) % 9 = 0 := by
      have h1 : m % 3 = 1 ∨ m % 3 = 2 := by 
        omega
      have h11 : m % 9 = 0 ∨ m % 9 = 1 ∨ m % 9 = 2 ∨ m % 9 = 3 ∨ m % 9 = 4 ∨ m % 9 = 5 ∨ m % 9 = 6 ∨ m % 9 = 7 ∨ m % 9 = 8 := by 
        omega
      rcases h11 with (h | h | h | h | h | h | h | h | h) <;> simp [h, pow_succ, Int.add_emod, Int.mul_emod, Int.sub_emod] <;> omega
    have h4 : 360 ∣ m^5 - 5 * m^3 + 4 * m := by 
      omega
    rw [hm] 
    exact h4
  · -- Show 360 is greatest.
    intro k hk
    have h1 := hk 720 (by 
      use 4
      all_goals norm_num 
    )
    have h4 := hk 2520 (by 
      use 5
      all_goals norm_num 
    )
    have h6 : k ∣ 360 := by
      have h3 : k ∣ 720 := by
        exact h1
      have h4' : k ∣ 2520 := by
        exact h4
      have h9 : k ∣ Int.gcd (720 : ℤ) (2520 : ℤ) := by 
        apply Int.dvd_gcd 
        · exact h3 
        · exact h4'
      have h10 : Int.gcd (720 : ℤ) (2520 : ℤ) = 360 := by 
        norm_num [Int.gcd]
      rw [h10] at h9 
      exact h9
    have h2 : k ≤ 360 := by 
      exact Int.le_of_dvd (by norm_num) h6
    linarith 
  all_goals try { tauto } <;> norm_num
  all_goals try { tauto } <;> norm_num
  all_goals try { tauto } <;> norm_num
  all_goals try { tauto } <;> norm_num