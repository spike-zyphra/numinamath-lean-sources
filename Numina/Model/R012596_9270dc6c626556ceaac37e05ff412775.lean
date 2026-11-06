import Mathlib

theorem algebra_21664 {n : ℕ} (hn : n = 54321) :
    IsGreatest {x | x < n ∧ x ∣ n} 18107 := by
  rw [hn]
  constructor
  · -- Show 18107 is in the set
    constructor
    · -- Show 18107 < 54321
      norm_num
    · -- Show 18107 divides 54321
      norm_num
  · -- Show that 18107 is greatest in the set
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    -- Show x ≤ 18107
    by_contra h
    push_neg at h
    have h1 : x ≤ 54321 := by 
      exact Nat.le_of_dvd (by linarith) hx2
    -- Now x divides 54321, and 18107 < x ≤ 54321.
    -- If x divides 54321, then 54321 = x * k for some k.
    have h3 : x ∣ 54321 := hx2
    rcases h3 with ⟨k, hk⟩
    have h4 : k > 1 := by 
      nlinarith
    have h5 : k < 3 := by
      nlinarith
    have h6 : k = 2 := by 
      omega
    rw [h6] at hk
    -- Now x * 2 = 54321, which is a contradiction.
    have h7 : x * 2 = 54321 := by 
      linarith
    omega