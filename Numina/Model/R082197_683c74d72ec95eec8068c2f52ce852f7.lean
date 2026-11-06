import Mathlib

theorem number_theory_278754 :
    IsLeast {n | 0 < n ∧ 5 ∣ n ∧ 7 ∣ n ∧ n % 3 = 1} 70 := by
  constructor
  · -- Show that 70 belongs to the set
    exact ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  · -- Show that 70 is the least such element
    intro n hn
    rcases hn with ⟨hn_pos, hn_5, hn_7, hn_mod⟩
    have h1 : 35 ∣ n := by
      have h5 : 5 ∣ n := hn_5
      have h7 : 7 ∣ n := hn_7
      have h8 : Nat.Coprime 5 7 := by norm_num
      have h9 : Nat.lcm 5 7 ∣ n := by 
        apply Nat.lcm_dvd
        · exact h5
        · exact h7
      have h9' : 35 ∣ n := by 
        have h10 : Nat.lcm 5 7 = 35 := by 
          rfl
        rw [h10] at h9
        exact h9
      exact h9'
    have h10 : n ≥ 70 := by
      omega
    linarith