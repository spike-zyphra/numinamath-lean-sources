import Mathlib

theorem number_theory_181450 :
    {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ Nat.gcd a b * a + b ^ 2 = 10000}.ncard = 99 := by 
  have h1 : {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ Nat.gcd a b * a + b ^ 2 = 10000} = Finset.filter (fun p : ℕ × ℕ => 
    p.1 > 0 ∧ p.2 > 0 ∧ Nat.gcd p.1 p.2 * p.1 + p.2 ^ 2 = 10000) (Finset.Icc (0 : ℕ) 10000 ×ˢ Finset.Icc (0 : ℕ) 100) := by
    ext ⟨a, b⟩
    simp
    intro ha hb he
    have h4 : b ≤ 100 := by
      by_contra h 
      push_neg at h 
      have h5 : b ≥ 101 := by omega 
      have h6 : b ^ 2 > 10000 := by
        nlinarith 
      have h7 : Nat.gcd a b * a ≥ 0 := by
        omega
      nlinarith [Nat.gcd_pos_of_pos_left a (show 0 < b by omega), sq_nonneg (a), sq_nonneg (b)]
    have h4' : a ≤ 10000 := by
      have h9 : b ≤ 100 := h4
      have h10 : Nat.gcd a b * a ≤ 10000 := by 
        have h11 : Nat.gcd a b * a + b ^ 2 = 10000 := he
        have h12 : b ^ 2 ≥ 0 := by
          omega
        omega 
      have h14 : Nat.gcd a b ≥ 1 := by
        apply Nat.gcd_pos_of_pos_left
        omega
      nlinarith [Nat.gcd_pos_of_pos_left a (show 0 < b by omega)]
    simp [h4', h4]
    <;> tauto 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide