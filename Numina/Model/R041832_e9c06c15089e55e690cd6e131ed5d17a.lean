import Mathlib

theorem number_theory_133475 :
    Set.ncard {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ a < b ∧ Nat.gcd a b = 2 ∧ Nat.lcm a b = 660} = 8 := by
  have h1 : {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ a < b ∧ Nat.gcd a b = 2 ∧ Nat.lcm a b = 660} = Finset.filter (fun p => p.1 > 0 ∧ p.2 > 0 ∧ p.1 < p.2 ∧ Nat.gcd p.1 p.2 = 2 ∧ Nat.lcm p.1 p.2 = 660) (Finset.Icc (0 : ℕ) 660 ×ˢ Finset.Icc (0 : ℕ) 660) := by
    ext ⟨a, b⟩
    simp
    intro ha hb hab h2 h3
    have h4 : a ≤ 660 := by
      have h1 : a ∣ Nat.lcm a b := Nat.dvd_lcm_left a b
      rw [h3] at h1
      exact Nat.le_of_dvd (by linarith) h1
    have h5 : b ≤ 660 := by
      have h1 : b ∣ Nat.lcm a b := Nat.dvd_lcm_right a b
      rw [h3] at h1
      exact Nat.le_of_dvd (by linarith) h1
    tauto
  rw [h1] at *
  rw [Set.ncard_coe_Finset]
  native_decide