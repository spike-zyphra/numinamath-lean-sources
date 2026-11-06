import Mathlib

theorem algebra_10372 {n : ℕ} (hn : n = 9879) :
    IsGreatest {p | p.Prime ∧ p ∣ n} 89 := by 
  rw [hn]
  constructor
  · -- Show 89 is in the set
    constructor
    · -- Show 89 is prime 
      norm_num
    · -- Show 89 divides 9879
      norm_num
  · -- Show there is no greater element in the set
    intro p hp
    rcases hp with ⟨h_prime, h_div⟩
    by_contra h
    push_neg at h
    have h1 : p ∣ 9879 := h_div
    have h2 : p ∣ 3 * 37 * 89 := by 
      have h3 : 3 * 37 * 89 = 9879 := by norm_num 
      rw [show 3 * 37 * 89 = 9879 by norm_num] 
      exact h1 
    have h3 : p ∣ 3 ∨ p ∣ 37 ∨ p ∣ 89 := by
      have h4 : p ∣ 3 * 37 * 89 := h2 
      have h4a : p ∣ 3 ∨ p ∣ (37 * 89) := by 
        apply (Nat.Prime.dvd_mul h_prime).mp 
        exact h4 
      cases h4a with 
      | inl h4b => 
        tauto 
      | inr h4b => 
        have h5 : p ∣ 37 ∨ p ∣ 89 := by 
          apply (Nat.Prime.dvd_mul h_prime).mp 
          exact h4b 
        tauto 
    rcases h3 with h3 | h37 | h89 
    · -- Assume p divides 3 
      have h3' : p ≤ 3 := by 
        exact Nat.le_of_dvd (by norm_num) h3 
      omega 
    · -- Assume p divides 37 
      have h37' : p ≤ 37 := by 
        exact Nat.le_of_dvd (by norm_num) h37 
      omega 
    · -- Assume p divides 89 
      have h89' : p ≤ 89 := by 
        exact Nat.le_of_dvd (by norm_num) h89 
      omega