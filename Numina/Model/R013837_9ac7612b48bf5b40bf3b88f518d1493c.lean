import Mathlib

theorem number_theory_269937 (a b : ℕ) :
    Nat.gcd a b = 30 - a ∧ Nat.gcd a b = 42 - b ↔
    (a = 29 ∧ b = 41) ∨ (a = 27 ∧ b = 39) := by
  constructor
  · -- Assume Nat.gcd a b = 30 - a ∧ Nat.gcd a b = 42 - b, prove (a = 29 ∧ b = 41) ∨ (a = 27 ∧ b = 39)
    rintro ⟨h1, h2⟩
    have h4 : a < 30 := by
      by_contra h
      push_neg at h
      have h5 : 30 - a = 0 := by
        omega
      have h5' : Nat.gcd a b = 0 := by
        omega
      have h7 : a = 0 ∧ b = 0 := by
        rw [Nat.gcd_eq_zero_iff] at h5'
        omega
      omega
    -- Show that b < 42
    have h5 : b < 42 := by 
      by_contra h
      push_neg at h 
      have h5 : 42 - b = 0 := by 
        omega
      have h5' : Nat.gcd a b = 0 := by 
        omega
      have h7 : a = 0 ∧ b = 0 := by 
        rw [Nat.gcd_eq_zero_iff] at h5' 
        omega
      omega
    have h6 : b = a + 12 := by 
      omega
    interval_cases a <;> norm_num [h6] at h1 h2 ⊢ 
      <;> omega
  · -- Assume the pairs satisfy the GCD conditions
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- Show that (29, 41) satisfy the GCD conditions
      constructor
      · -- Show that Nat.gcd 29 41 = 30 - 29
        norm_num [Nat.gcd]
      · -- Show that Nat.gcd 29 41 = 42 - 41
        norm_num [Nat.gcd]
    · -- Show that (27, 39) satisfy the GCD conditions
      constructor
      · -- Show that Nat.gcd 27 39 = 30 - 27
        norm_num [Nat.gcd]
      · -- Show that Nat.gcd 27 39 = 42 - 39
        norm_num [Nat.gcd]