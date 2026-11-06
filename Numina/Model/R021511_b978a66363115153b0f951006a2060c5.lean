import Mathlib

theorem number_theory_37305 :
    {(a, b, c) : ℤ × ℤ × ℤ | 1 ≤ a ∧ a ≤ 12 ∧ 1 ≤ b ∧ b ≤ 12 ∧ 1 ≤ c ∧ c ≤ 12 ∧
      ∃ q : ℚ, q > 0 ∧ q.num % 13 = 0 ∧ q = a + 1 / b - 1 / (b + 1 / c)}.ncard = 132 := by
  have h1 : {(a, b, c) : ℤ × ℤ × ℤ | 1 ≤ a ∧ a ≤ 12 ∧ 1 ≤ b ∧ b ≤ 12 ∧ 1 ≤ c ∧ c ≤ 12 ∧
      ∃ q : ℚ, q > 0 ∧ q.num % 13 = 0 ∧ q = a + 1 / b - 1 / (b + 1 / c)} = Finset.filter (fun s : ℤ × ℤ × ℤ => 
      let (a, b, c) := s
      1 ≤ a ∧ a ≤ 12 ∧ 1 ≤ b ∧ b ≤ 12 ∧ 1 ≤ c ∧ c ≤ 12 ∧
        let q := (a : ℚ) + (1 : ℚ) / (b : ℚ) - (1 : ℚ) / ((b : ℚ) + (1 : ℚ) / (c : ℚ))
        q > 0 ∧ q.num % 13 = 0 ∧ q = (a : ℚ) + (1 : ℚ) / (b : ℚ) - (1 : ℚ) / ((b : ℚ) + (1 : ℚ) / (c : ℚ))
    ) (Finset.Icc (1 : ℤ) 12 ×ˢ Finset.Icc (1 : ℤ) 12 ×ˢ Finset.Icc (1 : ℤ) 12) := by 
    ext ⟨a, b, c⟩
    simp
    <;> omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide