import Mathlib

theorem number_theory_3500 : {p : ℕ | p.Prime ∧ p ∣ (34^4 - 6 * 34^2 + 25) ∧ p ∈ Finset.Icc 1000 9999} = {1297} := by 
  ext p 
  simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- Assume p is in the left side, need to show p = 1297
    intro h
    rcases h with ⟨h_prime, h_div, ⟨h1000, h9999⟩⟩
    have h1 : (34^4 - 6 * 34^2 + 25 : ℕ) = 1297 * 1025 := by
      norm_num
    have h12 : p ∣ 1297 * 1025 := by
      rw [h1] at h_div
      exact h_div
    have h13 : p ∣ 1297 ∨ p ∣ 1025 := by
      have h14 : p ∣ 1297 * 1025 := h12
      have h15 : p ∣ 1297 ∨ p ∣ 1025 := by 
        apply (Nat.Prime.dvd_mul h_prime).1 at h14 
        tauto 
      exact h15
    rcases h13 with (h16 | h17)
    · -- Case where p divides 1297.
      have h18 : p ≤ 1297 := by
        exact Nat.le_of_dvd (by linarith) h16
      interval_cases p <;> norm_num at h16 h_prime ⊢ 
    · -- Case where p divides 1025.
      have h18 : p ∣ 1025 := h17 
      have h19 : p ∣ 5 ∨ p ∣ 41 := by 
        have h20 : p ∣ 1025 := h18 
        have h21 : p ∣ 5 ∨ p ∣ 205 := by 
          have h19a : p ∣ 5 * 205 := by 
            norm_num at h20 ⊢ 
            all_goals try exact h20 
          apply (Nat.Prime.dvd_mul h_prime).1 at h19a 
          tauto 
        rcases h21 with (h22 | h23)
        · -- Case where p divides 5.
          tauto 
        · -- Case where p divides 205.
          have h24 : p ∣ 205 := h23 
          have h25 : p ∣ 5 ∨ p ∣ 41 := by 
            have h205a : p ∣ 5 * 41 := by 
              norm_num at h24 ⊢ 
              all_goals try exact h24 
            apply (Nat.Prime.dvd_mul h_prime).1 at h205a 
            tauto 
          tauto 
      rcases h19 with (h20 | h21)
      · -- Case where p divides 5. 
        -- This implies p = 5, which contradicts 1000 ≤ p.
        have h22 : p ≤ 5 := by
          exact Nat.le_of_dvd (by linarith) h20
        interval_cases p <;> norm_num at h20 h_prime ⊢ 
      · -- Case where p divides 41.
        -- This implies p = 41, which contradicts 1000 ≤ p.
        have h23 : p ≤ 41 := by
          exact Nat.le_of_dvd (by linarith) h21
        interval_cases p <;> norm_num at h21 h_prime ⊢
  · -- Show 1297 is in the left side.
    intro hp
    rw [hp]
    constructor
    · -- 1297 is prime.
      norm_num
    constructor 
    · -- 1297 divides (34^4 - 6 * 34^2 + 25)
      norm_num
    · -- 1297 ∈ Finset.Icc 1000 9999
      all_goals norm_num