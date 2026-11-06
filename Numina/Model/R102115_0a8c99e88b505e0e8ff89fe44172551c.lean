import Mathlib

theorem algebra_284935 : {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ (a + 1 / b : ℚ) / (1 / a + b : ℚ) = 13 ∧ a + b ≤ 100}.ncard = 7 := by 
  have h1 : {(a, b) : ℕ × ℕ | a > 0 ∧ b > 0 ∧ (a + 1 / b : ℚ) / (1 / a + b : ℚ) = 13 ∧ a + b ≤ 100} = Finset.filter (fun s => 
    (s.1 > 0 ∧ s.2 > 0 ∧ (s.1 + 1 / s.2 : ℚ) / (1 / s.1 + s.2 : ℚ) = 13 ∧ s.1 + s.2 ≤ 100)
  ) (Finset.Icc (0 : ℕ) 100 ×ˢ Finset.Icc (0 : ℕ) 100
  ) := by 
    ext ⟨a, b⟩
    simp
    omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide