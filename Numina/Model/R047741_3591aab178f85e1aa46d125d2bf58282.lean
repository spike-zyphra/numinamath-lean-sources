import Mathlib

theorem number_theory_300391 :
    {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ Nat.lcm a b = 465696}.encard = 1155 := by 
  have h1 : {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ Nat.lcm a b = 465696} = Finset.filter (fun p : ℕ × ℕ => p.1 > 0 ∧ p.2 > 0 ∧ Nat.lcm p.1 p.2 = 465696) (Nat.divisors 465696 ×ˢ Nat.divisors 465696) := by
    ext ⟨a, b⟩
    simp
    intro h_a h_b h_lcm
    have h3 : a ∣ 465696 := by
      have h3 : a ∣ Nat.lcm a b := by
        exact Nat.dvd_lcm_left a b
      have h4 : Nat.lcm a b = 465696 := h_lcm
      have h4' : a ∣ 465696 := by
        rw [h4] at h3
        exact h3
      exact h4'
    have h4 : b ∣ 465696 := by
      have h4 : b ∣ Nat.lcm a b := by
        exact Nat.dvd_lcm_right a b
      have h5 : Nat.lcm a b = 465696 := h_lcm
      have h5' : b ∣ 465696 := by
        rw [h5] at h4
        exact h4
      exact h5'
    have h5 : a ≤ 465696 := by
      exact Nat.le_of_dvd (by norm_num) h3
    have h6 : b ≤ 465696 := by
      exact Nat.le_of_dvd (by norm_num) h4
    have h3' : a ∈ Nat.divisors 465696 := by
      simp [Nat.mem_divisors, h3, h5]
    have h4' : b ∈ Nat.divisors 465696 := by
      simp [Nat.mem_divisors, h4, h6]
    tauto
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide