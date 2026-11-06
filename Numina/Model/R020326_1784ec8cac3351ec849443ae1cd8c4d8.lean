import Mathlib

theorem number_theory_287048 : IsGreatest {p | p.Prime ∧ p ∣ ∑ k in Finset.Icc 1 11, k^5} 263 := by 
  constructor
  · -- Show 263 is in the set
    constructor
    · -- Show 263 is prime 
      norm_num
    · -- Show 263 divides the sum.
      have h5 : ∑ k in Finset.Icc 1 11, k^5 = 381876 := by
        native_decide
      rw [h5]
      norm_num
  · -- Show 263 is greatest
    intro p hp
    rcases hp with ⟨h1, h2⟩
    have h7 : p ∣ 381876 := by
      have h8 : ∑ k in Finset.Icc 1 11, k^5 = 381876 := by 
        native_decide
      rw [h8] at h2 
      exact h2
    by_contra h 
    push_neg at h 
    have h8 : p ∣ 263 ∨ p ∣ 1452 := by 
      have h61 : p ∣ 263 * 1452 := by 
        norm_num at h7 ⊢ 
        exact h7 
      have h62 : p ∣ 263 ∨ p ∣ 1452 := by 
        apply (Nat.Prime.dvd_mul h1).mp 
        simpa using h61 
      tauto 
    rcases h8 with (h9 | h9) 
    · -- Assume p divides 263
      have h10 : p ∣ 263 := h9 
      have h11 : p ≤ 263 := by 
        exact Nat.le_of_dvd (by norm_num) h10 
      nlinarith 
    · -- Assume p divides 1452 
      have h12 : p ∣ 1452 := h9 
      have h13 : p ≤ 1452 := by 
        exact Nat.le_of_dvd (by norm_num) h12 
      interval_cases p <;> norm_num at h1 h12 <;> all_goals contradiction