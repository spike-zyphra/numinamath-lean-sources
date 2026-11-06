import Mathlib

theorem number_theory_250779_a :
    {(a, b, c, d, e) : ℕ × ℕ × ℕ × ℕ × ℕ | 
      a > 0 ∧ a < 10 ∧ b < 10 ∧ c < 10 ∧ d < 10 ∧ e < 10 ∧
      Nat.ofDigits 10 [7, e, d, c, b, a] * 5 = Nat.ofDigits 10 [e, d, c, b, a, 7]} 
    = {(1, 4, 2, 8, 5)} := by 
  ext ⟨a, b, c, d, e⟩ 
  simp [Nat.ofDigits, Finset.sum] 
  constructor
  · -- Forward direction: If (a, b, c, d, e) is in the set, it must be (1, 4, 2, 8, 5).
    rintro ⟨ha1, ha2, hb1, hc1, hd1, he1, heq⟩
    omega
  · -- Backward direction: If (a, b, c, d, e) is (1, 4, 2, 8, 5), it's in the set.
    rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    all_goals norm_num [Nat.ofDigits, Finset.sum]

theorem number_theory_250779_b :
    {(a, b, c, d, e) : ℕ × ℕ × ℕ × ℕ × ℕ | 
      a > 0 ∧ a < 10 ∧ b < 10 ∧ c < 10 ∧ d < 10 ∧ e < 10 ∧
      Nat.ofDigits 10 [e, d, c, b, a, 1] * 3 = Nat.ofDigits 10 [1, e, d, c, b, a]} 
    = {(4, 2, 8, 5, 7)} := by 
  ext ⟨a, b, c, d, e⟩ 
  simp [Nat.ofDigits, Finset.sum]
  constructor
  · -- Forward direction: If (a, b, c, d, e) is in the set, it must be (4, 2, 8, 5, 7).
    rintro ⟨ha1, ha2, hb1, hc1, hd1, he1, heq⟩
    omega
  · -- Backward direction: If (a, b, c, d, e) is (4, 2, 8, 5, 7), it's in the set.
    rintro ⟨rfl, rfl, rfl, rfl, rfl⟩ 
    all_goals norm_num [Nat.ofDigits, Finset.sum]