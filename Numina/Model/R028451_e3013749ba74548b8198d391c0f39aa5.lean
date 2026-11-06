import Mathlib

theorem number_theory_173761 :
    Set.ncard {p : ℕ × ℕ | p.1 > 0 ∧ p.2 > 0 ∧ p.1 ≤ p.2 ∧ Nat.lcm p.1 p.2 = 2004} = 23 := by
  have : {p : ℕ × ℕ | p.1 > 0 ∧ p.2 > 0 ∧ p.1 ≤ p.2 ∧ Nat.lcm p.1 p.2 = 2004} = Finset.filter (fun p : ℕ × ℕ => p.1 > 0 ∧ p.2 > 0 ∧ p.1 ≤ p.2 ∧ Nat.lcm p.1 p.2 = 2004) (Finset.Icc (0 : ℕ) 2004 ×ˢ Finset.Icc (0 : ℕ) 2004) := by
    ext ⟨a, b⟩
    simp
    intro h1 h2 h3 h4
    have h5 : a ≤ 2004 := by 
      have h6 : a ∣ Nat.lcm a b := by 
        exact Nat.dvd_lcm_left a b
      rw [show Nat.lcm a b = 2004 by linarith] at h6
      have h7 : a ≤ 2004 := by
        exact Nat.le_of_dvd (by linarith) h6
      linarith
    have h8 : b ≤ 2004 := by 
      have h9 : b ∣ Nat.lcm a b := by 
        exact Nat.dvd_lcm_right a b
      rw [show Nat.lcm a b = 2004 by linarith] at h9
      have h10 : b ≤ 2004 := by 
        exact Nat.le_of_dvd (by linarith) h9
      linarith
    tauto
  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide