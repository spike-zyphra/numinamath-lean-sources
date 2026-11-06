import Mathlib

theorem number_theory_2123 :
    Set.ncard {p : ℕ × ℕ | p.1 * p.2 ∣ 48 ∧ Nat.gcd p.1 p.2 ≠ 1 ∧ 1 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ 48 ∧ p.1 ≠ p.2} = 16 := by
  have h1' : {p : ℕ × ℕ | p.1 * p.2 ∣ 48 ∧ Nat.gcd p.1 p.2 ≠ 1 ∧ 1 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ 48 ∧ p.1 ≠ p.2} = Finset.filter (fun p : ℕ × ℕ => p.1 * p.2 ∣ 48 ∧ Nat.gcd p.1 p.2 ≠ 1 ∧ 1 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ 48 ∧ p.1 ≠ p.2) (Finset.Icc (0 : ℕ) 48 ×ˢ Finset.Icc (0 : ℕ) 48) := by 
    ext ⟨a, b⟩ 
    simp 
    intro h1 h2 h3 h4 h5 
    have h8 : a ≤ 48 := by 
      have h12 : a * b ∣ 48 := h1 
      have h13 : a * b ≤ 48 := by 
        exact Nat.le_of_dvd (by norm_num) h12 
      have h7 : b ≥ 1 := by 
        by_contra h
        push_neg at h 
        have : b = 0 := by 
          omega 
        rw [this] at h1 
        simp at h1 
        all_goals linarith
      nlinarith 
    have h9 : b ≤ 48 := by 
      have h12 : a * b ∣ 48 := h1 
      have h13 : a * b ≤ 48 := by 
        exact Nat.le_of_dvd (by norm_num) h12 
      have h7 : a ≥ 1 := by 
        by_contra h
        push_neg at h 
        have : a = 0 := by 
          omega 
        rw [this] at h1 
        simp at h1 
        all_goals linarith 
      nlinarith 
    tauto 
  rw [h1']
  rw [Set.ncard_coe_Finset]
  native_decide